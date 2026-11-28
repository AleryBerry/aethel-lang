const std = @import("std");
const parser = @import("parser.zig");
const sema = @import("sema.zig");
const mir = @import("mir.zig");
const module_loader = @import("module_loader.zig");
const rust_ffi = @import("rust_ffi.zig");
const codegen_zig = @import("codegen_zig.zig");
const Io = std.Io;

fn analyzeOk(source: [:0]const u8) !sema.CheckedModule {
    var tree = try parser.parse(std.testing.allocator, source);
    defer tree.deinit();
    if (tree.hasErrors()) return error.ParseFailed;
    const checked = try sema.analyze(std.testing.allocator, &tree);
    if (checked.hasErrors()) {
        for (checked.diagnostics) |d| {
            std.debug.print("unexpected sema diagnostic ({s}): {s}\n", .{ @tagName(d.kind), d.message });
        }
        return error.SemaFailed;
    }
    return checked;
}

fn expectSemaError(source: [:0]const u8, expected_kind: sema.SemaDiagnostic.Kind) !void {
    var tree = try parser.parse(std.testing.allocator, source);
    defer tree.deinit();
    if (tree.hasErrors()) return error.ParseFailed;
    var checked = try sema.analyze(std.testing.allocator, &tree);
    defer checked.deinit();
    for (checked.diagnostics) |d| {
        if (d.kind == expected_kind) return;
    }
    std.debug.print("expected sema diagnostic {s}, got {d} diagnostic(s)\n", .{
        @tagName(expected_kind),
        checked.diagnostics.len,
    });
    return error.ExpectedSemaErrorMissing;
}

fn compileToZig(source: [:0]const u8) ![]u8 {
    var tree = try parser.parse(std.testing.allocator, source);
    defer tree.deinit();
    if (tree.hasErrors()) return error.ParseFailed;
    var checked = try sema.analyze(std.testing.allocator, &tree);
    defer checked.deinit();
    if (checked.hasErrors()) {
        for (checked.diagnostics) |d| {
            std.debug.print("unexpected sema error ({s}): {s}\n", .{ @tagName(d.kind), d.message });
        }
        return error.SemaFailed;
    }
    var buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer buf.deinit();
    try codegen_zig.emitZig(&tree, &checked, &buf.writer);
    return try buf.toOwnedSlice();
}

test "1. Stage E: exhaustive case acceptance across bool, Option, Result, ADT, and Int(lo..=hi)" {
    var ok = try analyzeOk(
        \\type Color { Red, Green, Blue }
        \\fn check_bool(b: bool) -> u8 {
        \\  case b {
        \\    true -> 1
        \\    false -> 0
        \\  }
        \\}
        \\fn check_opt(o: Option(i32)) -> i32 {
        \\  case o {
        \\    Some(v) -> v
        \\    None -> -1
        \\  }
        \\}
        \\fn check_res(r: Result(i32, u8)) -> i32 {
        \\  case r {
        \\    Ok(x) -> x
        \\    Err(e) -> 0 -% (e as i32)
        \\  }
        \\}
        \\fn check_adt(c: Color) -> u8 {
        \\  case c {
        \\    Red | Green -> 1
        \\    Blue -> 2
        \\  }
        \\}
        \\fn check_int_range(hp: Int(0..=100)) -> u8 {
        \\  case hp {
        \\    0 -> 0
        \\    1..=49 -> 1
        \\    50..=100 -> 2
        \\  }
        \\}
        \\fn check_pair(a: u8, b: u8) -> u8 {
        \\  case a, b {
        \\    0, 0 -> 1
        \\    _, _ -> 2
        \\  }
        \\}
    );
    defer ok.deinit();
}

test "2. Stage E: non-exhaustive case rejections pinpoint missing patterns" {
    try expectSemaError(
        \\fn bad_bool(b: bool) -> u8 {
        \\  case b {
        \\    true -> 1
        \\  }
        \\}
    , .non_exhaustive_match);

    try expectSemaError(
        \\fn bad_opt(o: Option(i32)) -> i32 {
        \\  case o {
        \\    Some(x) -> x
        \\  }
        \\}
    , .non_exhaustive_match);

    try expectSemaError(
        \\fn bad_res(r: Result(i32, u8)) -> i32 {
        \\  case r {
        \\    Ok(v) -> v
        \\  }
        \\}
    , .non_exhaustive_match);

    try expectSemaError(
        \\type State { Ready, Busy, Failed }
        \\fn bad_adt(s: State) -> u8 {
        \\  case s {
        \\    Ready -> 1
        \\    Busy -> 2
        \\  }
        \\}
    , .non_exhaustive_match);

    try expectSemaError(
        \\fn bad_gap(hp: Int(0..=100)) -> u8 {
        \\  case hp {
        \\    0..=49 -> 1
        \\    51..=100 -> 2
        \\  }
        \\}
    , .non_exhaustive_match);

    try expectSemaError(
        \\fn bad_guarded_only(b: bool) -> u8 {
        \\  case b {
        \\    true if 1 < 2 -> 1
        \\    false -> 0
        \\  }
        \\}
    , .non_exhaustive_match);
}

test "3. Stage E: Option & Result case codegen and complete Int(0..=100) switch" {
    const zig_src = try compileToZig(
        \\fn unwrap_or_zero(o: Option(i32)) -> i32 {
        \\  case o {
        \\    Some(v) -> v +% 1
        \\    None -> 0
        \\  }
        \\}
        \\fn result_score(r: Result(i32, u8)) -> i32 {
        \\  case r {
        \\    Ok(val) -> val
        \\    Err(_) -> -1
        \\  }
        \\}
        \\fn bucket(hp: Int(0..=100)) -> u8 {
        \\  case hp {
        \\    0..=49 -> 1
        \\    50..=100 -> 2
        \\  }
        \\}
    );
    defer std.testing.allocator.free(zig_src);

    try std.testing.expect(std.mem.indexOf(u8, zig_src, "if (__opt_") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "switch (r) {") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ".Ok => |val| val,") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "0...49 =>") != null);
}

test "4. Stage E: multi-file module_loader, qualified/unqualified imports, diamond dedup, visibility & cycles" {
    const files = [_]module_loader.MemoryFile{
        .{
            .module_key = "core/shared",
            .path = "core/shared.aethel",
            .source =
            \\pub const OFFSET: i32 = 5
            \\pub fn add_off(x: i32) -> i32 { x +% OFFSET }
            ,
        },
        .{
            .module_key = "math",
            .path = "math.aethel",
            .source =
            \\import core/shared
            \\fn secret(x: i32) -> i32 { x +% 100 }
            \\pub fn helper(x: i32) -> i32 { shared.add_off(x) }
            ,
        },
        .{
            .module_key = "geom/vec",
            .path = "geom/vec.aethel",
            .source =
            \\import core/shared
            \\pub type Vec2 { x: i32, y: i32 }
            \\pub fn sum(v: Vec2) -> i32 { shared.add_off(v.x +% v.y) }
            ,
        },
        .{
            .module_key = "main",
            .path = "main.aethel",
            .source =
            \\import math.{helper}
            \\import geom/vec as v2
            \\fn main() -> i32 {
            \\  let p = v2.Vec2 { x: 3, y: 4 }
            \\  helper(v2.sum(p))
            \\}
            ,
        },
    };

    var loaded = try module_loader.loadFromMemory(std.testing.allocator, "main", &files);
    defer loaded.deinit();
    try std.testing.expect(!loaded.hasErrors());
    // Diamond dependency `core/shared` loaded exactly once -> 4 slices total.
    try std.testing.expectEqual(@as(usize, 4), loaded.slices.len);

    var tree = try parser.parse(std.testing.allocator, loaded.combined_source);
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());

    var mod_infos: [4]sema.ModuleSliceInfo = undefined;
    for (loaded.slices, 0..) |sl, idx| {
        mod_infos[idx] = .{
            .module_id = sl.module_id,
            .module_key = sl.module_key,
            .start = sl.start,
            .end = sl.end,
        };
    }
    var checked = try sema.analyzeWithModules(std.testing.allocator, &tree, &mod_infos, loaded.entry_module_id);
    defer checked.deinit();
    try std.testing.expect(!checked.hasErrors());

    var zig_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer zig_buf.deinit();
    try codegen_zig.emitZig(&tree, &checked, &zig_buf.writer);
    const zig_src = zig_buf.written();
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "mod__math__helper(") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "mod__geom_vec__Vec2") != null);

    // Visibility error: accessing non-pub `math.secret`.
    const priv_files = [_]module_loader.MemoryFile{
        files[0],
        files[1],
        .{
            .module_key = "main",
            .path = "main.aethel",
            .source =
            \\import math
            \\fn bad() -> i32 { math.secret(1) }
            ,
        },
    };
    var priv_loaded = try module_loader.loadFromMemory(std.testing.allocator, "main", &priv_files);
    defer priv_loaded.deinit();
    var ptree = try parser.parse(std.testing.allocator, priv_loaded.combined_source);
    defer ptree.deinit();
    const p_infos = try std.testing.allocator.alloc(sema.ModuleSliceInfo, priv_loaded.slices.len);
    defer std.testing.allocator.free(p_infos);
    for (priv_loaded.slices, 0..) |sl, idx| {
        p_infos[idx] = .{ .module_id = sl.module_id, .module_key = sl.module_key, .start = sl.start, .end = sl.end };
    }
    var pchecked = try sema.analyzeWithModules(std.testing.allocator, &ptree, p_infos, priv_loaded.entry_module_id);
    defer pchecked.deinit();
    var saw_vis = false;
    for (pchecked.diagnostics) |d| {
        if (d.kind == .visibility_error) saw_vis = true;
    }
    try std.testing.expect(saw_vis);

    // Circular import detection: a -> b -> a.
    const cycle_files = [_]module_loader.MemoryFile{
        .{ .module_key = "a", .path = "a.aethel", .source = "import b\npub fn fa() -> u8 { 1 }" },
        .{ .module_key = "b", .path = "b.aethel", .source = "import a\npub fn fb() -> u8 { 2 }" },
    };
    var cyc_loaded = try module_loader.loadFromMemory(std.testing.allocator, "a", &cycle_files);
    defer cyc_loaded.deinit();
    try std.testing.expect(cyc_loaded.hasErrors());
}

test "5. Stage E: Rust FFI slice aliasing, RustOwn single-drop, and C-ABI bridge codegen" {
    // Disjoint half-open &mut slices accepted + mutable->immutable coercion allowed.
    var ok = try analyzeOk(
        \\opaque type RustBuf
        \\extern "rust" {
        \\  fn fast_dot(xs: [f32], ys: [f32]) -> f32
        \\  fn scale_two(lhs: [mut f32], rhs: [mut f32], k: f32)
        \\  fn rust_buf_new() -> RustBuf
        \\  fn rust_buf_sum(b: View(RustBuf, Shared)) -> i32
        \\  fn rust_buf_drop(b: RustBuf)
        \\}
        \\fn run_ok(mut arr: [mut f32], mid: u32) -> f32 {
        \\  scale_two(arr[0..mid], arr[mid..arr.len], 2.0)
        \\  let b = rust_buf_new()
        \\  let _ = rust_buf_sum(b)
        \\  rust_buf_drop(b)
        \\  fast_dot(arr, arr)
        \\}
    );
    defer ok.deinit();

    // Overlapping &mut slices rejected with borrow_conflict.
    try expectSemaError(
        \\extern "rust" fn scale_two(lhs: [mut f32], rhs: [mut f32], k: f32)
        \\fn bad_alias(mut arr: [mut f32]) {
        \\  scale_two(arr[0..3], arr[2..4], 2.0)
        \\}
    , .borrow_conflict);

    // Passing immutable slice where [mut T] is expected rejected with mutability_error.
    try expectSemaError(
        \\extern "rust" fn scale_one(xs: [mut f32])
        \\fn bad_mut(xs: [f32]) {
        \\  scale_one(xs)
        \\}
    , .mutability_error);

    // RustOwn double-drop / use-after-drop caught as use_after_move.
    try expectSemaError(
        \\opaque type RustBuf
        \\extern "rust" {
        \\  fn rust_buf_new() -> RustBuf
        \\  fn rust_buf_drop(b: RustBuf)
        \\}
        \\fn double_drop() {
        \\  let b = rust_buf_new()
        \\  rust_buf_drop(b)
        \\  rust_buf_drop(b)
        \\}
    , .use_after_move);

    // Non-C-ABI record parameter rejected with invalid_ffi_type.
    try expectSemaError(
        \\type Pt { x: i32, y: i32 }
        \\extern "rust" fn bad_rec(p: Pt) -> i32
    , .invalid_ffi_type);

    // Check Zig C-ABI emission & MIR skipping & Rust C-ABI adapter generation.
    const ffi_src: [:0]const u8 =
        \\opaque type RustBuf
        \\extern "rust" {
        \\  fn fast_dot(xs: [f32], ys: [f32]) -> f32
        \\  fn rust_buf_new() -> RustBuf
        \\  fn rust_buf_sum(b: View(RustBuf, Shared)) -> i32
        \\  fn rust_buf_drop(b: RustBuf)
        \\}
        \\fn use_ffi(a: [f32], b: [f32]) -> f32 {
        \\  let buf = rust_buf_new()
        \\  let _ = rust_buf_sum(buf)
        \\  rust_buf_drop(buf)
        \\  fast_dot(a, b)
        \\}
    ;
    var tree = try parser.parse(std.testing.allocator, ffi_src);
    defer tree.deinit();
    var checked = try sema.analyze(std.testing.allocator, &tree);
    defer checked.deinit();
    try std.testing.expect(!checked.hasErrors());

    var mir_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer mir_buf.deinit();
    try mir.emitMir(&checked, &mir_buf.writer);
    try std.testing.expect(std.mem.indexOf(u8, mir_buf.written(), "fn fast_dot") == null);
    try std.testing.expect(std.mem.indexOf(u8, mir_buf.written(), "fn use_ffi") != null);

    var zig_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer zig_buf.deinit();
    try codegen_zig.emitZig(&tree, &checked, &zig_buf.writer);
    const zig_src = zig_buf.written();
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "extern \"c\" fn fast_dot(xs_ptr: [*]const f32, xs_len: usize, ys_ptr: [*]const f32, ys_len: usize) f32;") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "extern \"c\" fn rust_buf_sum(b: ?*const anyopaque) i32;") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ".ptr, __ffi_") != null);

    var rust_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer rust_buf.deinit();
    try rust_ffi.emitRustAdapter(&tree, &checked, null, &rust_buf.writer);
    const rs_src = rust_buf.written();
    try std.testing.expect(std.mem.indexOf(u8, rs_src, "pub unsafe extern \"C\" fn fast_dot(") != null);
    try std.testing.expect(std.mem.indexOf(u8, rs_src, "core::slice::from_raw_parts(xs_ptr, xs_len)") != null);
    try std.testing.expect(std.mem.indexOf(u8, rs_src, "b: *const core::ffi::c_void") != null);
}
