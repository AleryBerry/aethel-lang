const std = @import("std");
const Io = std.Io;
const parser = @import("parser.zig");
const sema = @import("sema.zig");
const codegen_zig = @import("codegen_zig.zig");
const rust_ffi = @import("rust_ffi.zig");

test "1. Stage I: @derive(rust, ...), @rust_attr, bool extern struct, [FlatRec] slices, and View/slice callbacks" {
    const source: [:0]const u8 =
        \\@layout(flat)
        \\@derive(rust, "serde::Serialize", "serde::Deserialize", "PartialEq")
        \\pub type EngineConfig {
        \\  @rust_attr("serde(rename = \"target_fps\")")
        \\  pub fps: u32,
        \\  pub vsync: bool,
        \\}
        \\
        \\@layout(flat)
        \\@derive(rust, "bytemuck::Pod", "bytemuck::Zeroable")
        \\pub type GpuVertex {
        \\  pub x: f32,
        \\  pub y: f32,
        \\  pub color: u32,
        \\}
        \\
        \\@external(rust, "self", "submit_vertices")
        \\pub fn submit_vertices(verts: [GpuVertex]) -> u32
        \\
        \\@external(rust, "self", "visit_config")
        \\pub fn visit_config(cfg: EngineConfig, cb: fn(View(EngineConfig, Exclusive), [mut f32]) -> ())
        \\
        \\pub fn update_cfg(c: View(EngineConfig, Exclusive), lanes: [mut f32]) {
        \\  c.fps = 120u32
        \\  if lanes.len > 0 {
        \\    lanes[0] = lanes[0] + 1.0f32
        \\  }
        \\}
        \\
        \\pub fn main() {
        \\  let vs: [GpuVertex] = [GpuVertex { x: 1.0f32, y: 2.0f32, color: 0xff00ff00u32 }]
        \\  let _ = submit_vertices(vs)
        \\  let cfg = EngineConfig { fps: 60u32, vsync: true }
        \\  visit_config(cfg, update_cfg)
        \\}
    ;

    var tree = try parser.parse(std.testing.allocator, source);
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());

    const declared = [_][]const u8{ "serde", "bytemuck" };
    var checked = try sema.analyzeWithModulesAndManifest(
        std.testing.allocator,
        &tree,
        &.{},
        0,
        "stage_i_app",
        &declared,
    );
    defer checked.deinit();
    if (checked.hasErrors()) {
        for (checked.diagnostics) |d| std.debug.print("stage I test 1 sema err: {s}\n", .{d.message});
    }
    try std.testing.expect(!checked.hasErrors());

    var zig_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer zig_buf.deinit();
    try codegen_zig.emitZig(&tree, &checked, &zig_buf.writer);
    const zig_src = zig_buf.written();

    try std.testing.expect(std.mem.indexOf(u8, zig_src, "const EngineConfig = extern struct") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "aethelSyncAlloc") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "aethelPrint") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "*EngineConfig, noalias [*]f32, usize") != null);

    var rust_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer rust_buf.deinit();
    try rust_ffi.emitCargoProjectAdapter(&tree, &checked, null, "stage_i_app", &rust_buf.writer);
    const rust_src = rust_buf.written();

    try std.testing.expect(std.mem.indexOf(u8, rust_src, "#[derive(Copy, Clone, Debug, ::serde::Serialize, ::serde::Deserialize, PartialEq)]") != null);
    try std.testing.expect(std.mem.indexOf(u8, rust_src, "#[serde(rename = \"target_fps\")]") != null);
    try std.testing.expect(std.mem.indexOf(u8, rust_src, "#[derive(Copy, Clone, Debug, ::bytemuck::Pod, ::bytemuck::Zeroable)]") != null);
    try std.testing.expect(std.mem.indexOf(u8, rust_src, "verts_ptr: *const GpuVertex") != null);
    try std.testing.expect(std.mem.indexOf(u8, rust_src, "__c_0: &mut EngineConfig, __c_1: &mut [f32]") != null);
}

fn expectStageISemaError(
    source: [:0]const u8,
    pkg_name: ?[]const u8,
    declared_crates: ?[]const []const u8,
) !void {
    var tree = try parser.parse(std.testing.allocator, source);
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());

    var checked = try sema.analyzeWithModulesAndManifest(
        std.testing.allocator,
        &tree,
        &.{},
        0,
        pkg_name,
        declared_crates,
    );
    defer checked.deinit();
    try std.testing.expect(checked.hasErrors());
}

test "2. Stage I: negative proc-macro counterexamples (padded Pod, bool Pod, repr @rust_attr, non-flat derive, undeclared crate)" {
    const declared = [_][]const u8{ "bytemuck", "bevy" };

    // 1) Implicit padding struct { u8, u32 } rejected for bytemuck::Pod
    try expectStageISemaError(
        \\@layout(flat)
        \\@derive(rust, "bytemuck::Pod")
        \\pub type PaddedVertex {
        \\  pub tag: u8,
        \\  pub val: u32,
        \\}
        \\pub fn main() {}
    , "app", &declared);

    // 2) bool field rejected for bytemuck::Pod
    try expectStageISemaError(
        \\@layout(flat)
        \\@derive(rust, "bytemuck::Pod")
        \\pub type BoolVertex {
        \\  pub active: bool,
        \\}
        \\pub fn main() {}
    , "app", &declared);

    // 3) Layout-overriding @rust_attr("repr(packed)") rejected
    try expectStageISemaError(
        \\@layout(flat)
        \\@rust_attr("repr(packed)")
        \\pub type BadRepr {
        \\  pub x: u32,
        \\}
        \\pub fn main() {}
    , "app", &declared);

    // 4) Non-allowlisted proc-macro attribute @rust_attr("custom_rewriter") rejected
    try expectStageISemaError(
        \\@layout(flat)
        \\@rust_attr("custom_rewriter")
        \\pub type BadMacro {
        \\  pub x: u32,
        \\}
        \\pub fn main() {}
    , "app", &declared);

    // 5) @derive(rust, ...) on non-@layout(flat) record rejected
    try expectStageISemaError(
        \\@layout(soa)
        \\@derive(rust, "bevy::prelude::Component")
        \\pub type BadSoaComp {
        \\  pub x: f32,
        \\}
        \\pub fn main() {}
    , "app", &declared);

    // 6) Undeclared crate in @derive(rust, "serde::Serialize") rejected
    try expectStageISemaError(
        \\@layout(flat)
        \\@derive(rust, "serde::Serialize")
        \\pub type UndeclaredSerde {
        \\  pub x: u32,
        \\}
        \\pub fn main() {}
    , "app", &declared);
}

test "3. Stage I: Vec as_slice and as_mut_slice lowering over flat C-ABI records" {
    const source: [:0]const u8 =
        \\import std/vec
        \\
        \\@layout(flat)
        \\@derive(rust, "bytemuck::Pod", "bytemuck::Zeroable")
        \\pub type GpuVertex {
        \\  pub x: f32,
        \\  pub y: f32,
        \\  pub color: u32,
        \\}
        \\
        \\@external(rust, "self", "hash_verts")
        \\pub fn hash_verts(xs: [GpuVertex]) -> u32
        \\
        \\@external(rust, "self", "paint_verts")
        \\pub fn paint_verts(xs: [mut GpuVertex], rgba: u32)
        \\
        \\pub fn main() {
        \\  let mut verts: Vec(GpuVertex) = vec.with_capacity(4u64)
        \\  vec.push(verts, GpuVertex { x: 1.0f32, y: 2.0f32, color: 1u32 })
        \\  let _ = hash_verts(vec.as_slice(verts))
        \\  paint_verts(vec.as_mut_slice(verts), 99u32)
        \\}
    ;

    const declared = [_][]const u8{"bytemuck"};
    const files = [_]@import("module_loader.zig").MemoryFile{
        .{ .module_key = "main", .path = "main.aethel", .source = source },
    };
    var loaded = try @import("module_loader.zig").loadFromMemory(std.testing.allocator, "main", &files);
    defer loaded.deinit();
    try std.testing.expect(!loaded.hasErrors());

    var tree = try parser.parse(std.testing.allocator, loaded.combined_source);
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());

    const mod_infos = try std.testing.allocator.alloc(sema.ModuleSliceInfo, loaded.slices.len);
    defer std.testing.allocator.free(mod_infos);
    for (loaded.slices, 0..) |sl, idx| {
        mod_infos[idx] = .{ .module_id = sl.module_id, .module_key = sl.module_key, .start = sl.start, .end = sl.end };
    }

    var checked = try sema.analyzeWithModulesAndManifest(
        std.testing.allocator,
        &tree,
        mod_infos,
        loaded.entry_module_id,
        "vec_slice_app",
        &declared,
    );
    defer checked.deinit();
    if (checked.hasErrors()) {
        for (checked.diagnostics) |d| std.debug.print("stage I test 3 sema err: {s}\n", .{d.message});
    }
    try std.testing.expect(!checked.hasErrors());

    var zig_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer zig_buf.deinit();
    try codegen_zig.emitZig(&tree, &checked, &zig_buf.writer);
    const zig_src = zig_buf.written();
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ".asSlice()") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ".mutSlice()") != null);
}

test "Stage I 4: @layout(soa) map_in_place emits @Vector(8, T) column slice SIMD and selective fold" {
    const src =
        \\import std/vec
        \\
        \\@layout(soa)
        \\pub type Body {
        \\  pub px: f32,
        \\  pub py: f32,
        \\  pub vx: f32,
        \\  pub cold_id: u32,
        \\}
        \\
        \\fn step(cols: Collection(Body) ~> mut .{ px, vx }, dt: f32) {
        \\  cols |> map_in_place(fn(b) {
        \\    b.px = b.px + b.vx * dt
        \\  })
        \\}
        \\
        \\fn sum_px(cols: Collection(Body) ~>.{ px }) -> f32 {
        \\  cols |> fold(0.0f32, fn(s, b) { s + b.px })
        \\}
        \\
        \\pub fn main() -> i32 {
        \\  let mut v: Vec(Body) = vec.with_capacity(16u64)
        \\  vec.push(v, Body { px: 1.0f32, py: 2.0f32, vx: 3.0f32, cold_id: 7u32 })
        \\  step(vec.as_collection(v), 0.5f32)
        \\  let _t = sum_px(vec.as_collection(v))
        \\  0i32
        \\}
    ;
    const files = [_]@import("module_loader.zig").MemoryFile{
        .{ .module_key = "main", .path = "main.aethel", .source = src },
    };
    var loaded = try @import("module_loader.zig").loadFromMemory(std.testing.allocator, "main", &files);
    defer loaded.deinit();
    try std.testing.expect(!loaded.hasErrors());

    var tree = try parser.parse(std.testing.allocator, loaded.combined_source);
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());

    const mod_infos = try std.testing.allocator.alloc(sema.ModuleSliceInfo, loaded.slices.len);
    defer std.testing.allocator.free(mod_infos);
    for (loaded.slices, 0..) |sl, idx| {
        mod_infos[idx] = .{ .module_id = sl.module_id, .module_key = sl.module_key, .start = sl.start, .end = sl.end };
    }

    var checked = try sema.analyzeWithModules(std.testing.allocator, &tree, mod_infos, loaded.entry_module_id);
    defer checked.deinit();
    try std.testing.expect(!checked.hasErrors());

    var zig_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer zig_buf.deinit();
    try codegen_zig.emitZig(&tree, &checked, &zig_buf.writer);
    const zig_src = zig_buf.written();

    try std.testing.expect(std.mem.indexOf(u8, zig_src, "@Vector(8, f32)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "[__tile_1..][0..8].*") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__col_1.get(") == null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__col_1.set(") == null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__col_2.get(") == null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__col_1.cold_id[") == null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__col_2.cold_id[") == null);
}

test "Stage I 5: non-SIMD @layout(soa) map_in_place writes only modified columns and rust_ffi emits noalias helper" {
    const src =
        \\import std/vec
        \\
        \\@layout(soa)
        \\pub type Body2 {
        \\  pub px: f32,
        \\  pub vx: f32,
        \\  pub cold: u32,
        \\}
        \\
        \\@external(rust, "self", "rust_step")
        \\pub fn rust_step(q: Collection(Body2) ~> mut .{ px, vx }, dt: f32)
        \\
        \\fn bump_cond(cols: Collection(Body2) ~> mut .{ px, vx }) {
        \\  cols |> map_in_place(fn(b) {
        \\    let mut step = 0i32
        \\    while step < 1i32 {
        \\      b.px = b.px + b.vx
        \\      step = step + 1i32
        \\    }
        \\  })
        \\}
        \\
        \\pub fn main() -> i32 {
        \\  let mut v: Vec(Body2) = vec.with_capacity(8u64)
        \\  vec.push(v, Body2 { px: 0.0f32, vx: 1.0f32, cold: 99u32 })
        \\  bump_cond(vec.as_collection(v))
        \\  rust_step(vec.as_collection(v), 0.5f32)
        \\  0i32
        \\}
    ;
    const files = [_]@import("module_loader.zig").MemoryFile{
        .{ .module_key = "main", .path = "main.aethel", .source = src },
    };
    var loaded = try @import("module_loader.zig").loadFromMemory(std.testing.allocator, "main", &files);
    defer loaded.deinit();
    try std.testing.expect(!loaded.hasErrors());

    var tree = try parser.parse(std.testing.allocator, loaded.combined_source);
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());

    const mod_infos = try std.testing.allocator.alloc(sema.ModuleSliceInfo, loaded.slices.len);
    defer std.testing.allocator.free(mod_infos);
    for (loaded.slices, 0..) |sl, idx| {
        mod_infos[idx] = .{ .module_id = sl.module_id, .module_key = sl.module_key, .start = sl.start, .end = sl.end };
    }

    var checked = try sema.analyzeWithModules(std.testing.allocator, &tree, mod_infos, loaded.entry_module_id);
    defer checked.deinit();
    try std.testing.expect(!checked.hasErrors());

    var zig_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer zig_buf.deinit();
    try codegen_zig.emitZig(&tree, &checked, &zig_buf.writer);
    const zig_src = zig_buf.written();
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__col_1.px[__idx_1] = __el_1.px;") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__col_1.vx[__idx_1] =") == null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ".cold[__idx_1]") == null);

    var rust_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer rust_buf.deinit();
    try rust_ffi.emitRustAdapter(&tree, &checked, "pub fn rust_step(_q: Body2_px_vxQuery, _dt: f32) {}\n", &rust_buf.writer);
    const rust_src = rust_buf.written();
    try std.testing.expect(std.mem.indexOf(u8, rust_src, "#[inline(never)]\n    fn __aethel_soa_noalias_call<'a>(") != null);
}

test "Stage I 6: @select SIMD, +% SIMD fold, exact with_capacity, str.repeat, L1 bool unpack, PHI-free cb & Cross-LTO inline" {
    const src =
        \\import std/vec
        \\import std/str
        \\
        \\@layout(soa)
        \\pub type BodySimd {
        \\  pub px: f32,
        \\  pub vx: f32,
        \\  pub tag: u64,
        \\}
        \\
        \\@layout(auto)
        \\pub type SmallAuto {
        \\  pub hot_flag: bool,
        \\  pub flag_b: bool,
        \\  pub flag_c: bool,
        \\  pub hot_val: u8,
        \\}
        \\
        \\@layout(auto)
        \\pub type LargeAuto {
        \\  pub hot_flag: bool,
        \\  pub flag_b: bool,
        \\  pub flag_c: bool,
        \\  pub hot_val: u8,
        \\}
        \\
        \\@external(rust, "self", "rust_step_cb")
        \\pub fn rust_step_cb(q: Collection(BodySimd) ~> mut .{ px, vx }, cb: fn([f32]) -> f32) -> f32
        \\
        \\fn step_select(cols: Collection(BodySimd) ~> mut .{ px, vx }) {
        \\  cols |> map_in_place(fn(b) {
        \\    if b.vx > 0.0f32 {
        \\      b.px = b.px + b.vx
        \\    } else {
        \\      b.vx = b.vx * 0.5f32
        \\    }
        \\  })
        \\}
        \\
        \\fn fold_wrap(cols: Collection(BodySimd) ~>.{ tag }) -> u64 {
        \\  cols |> fold(0u64, fn(s, b) { s +% (b.tag +% 1u64) })
        \\}
        \\
        \\fn check_auto_small(cols: Collection(SmallAuto) ~>.{ hot_flag, hot_val }) -> u64 {
        \\  cols |> fold(0u64, fn(s, a) { if a.hot_flag { s +% (a.hot_val as u64) } else { s } })
        \\}
        \\
        \\fn check_auto_large(cols: Collection(LargeAuto) ~>.{ hot_flag, hot_val }) -> u64 {
        \\  cols |> fold(0u64, fn(s, a) { if a.hot_flag { s +% (a.hot_val as u64) } else { s } })
        \\}
        \\
        \\fn cb_sum(xs: [f32]) -> f32 {
        \\  xs[0]
        \\}
        \\
        \\fn scale_mut(xs: [mut f32], k: f32) {
        \\  xs[0] = xs[0] * k
        \\}
        \\
        \\pub fn main() -> i32 {
        \\  let mut v: Vec(BodySimd) = vec.with_capacity(64u64)
        \\  vec.push(v, BodySimd { px: 1.0f32, vx: 2.0f32, tag: 3u64 })
        \\  step_select(vec.as_collection(v))
        \\  let s1: u64 = fold_wrap(vec.as_collection(v))
        \\
        \\  let mut vs: Vec(SmallAuto) = vec.with_capacity(64u64)
        \\  vec.push(vs, SmallAuto { hot_flag: true, flag_b: false, flag_c: true, hot_val: 7u8 })
        \\  let a1: u64 = check_auto_small(vec.as_collection(vs))
        \\
        \\  let mut vl: Vec(LargeAuto) = vec.with_capacity(20000u64)
        \\  vec.push(vl, LargeAuto { hot_flag: true, flag_b: false, flag_c: true, hot_val: if a1 == 0u64 { 1u8 } else { 7u8 } })
        \\  let _ = check_auto_large(vec.as_collection(vl))
        \\
        \\  let rep = str.repeat("ab", 16u64)
        \\  let _ = str.len(rep)
        \\  let _ = rust_step_cb(vec.as_collection(v), cb_sum)
        \\  0i32
        \\}
    ;
    const files = [_]@import("module_loader.zig").MemoryFile{
        .{ .module_key = "main", .path = "main.aethel", .source = src },
    };
    var loaded = try @import("module_loader.zig").loadFromMemory(std.testing.allocator, "main", &files);
    defer loaded.deinit();
    try std.testing.expect(!loaded.hasErrors());

    var tree = try parser.parse(std.testing.allocator, loaded.combined_source);
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());

    const mod_infos = try std.testing.allocator.alloc(sema.ModuleSliceInfo, loaded.slices.len);
    defer std.testing.allocator.free(mod_infos);
    for (loaded.slices, 0..) |sl, idx| {
        mod_infos[idx] = .{ .module_id = sl.module_id, .module_key = sl.module_key, .start = sl.start, .end = sl.end };
    }

    var checked = try sema.analyzeWithModules(std.testing.allocator, &tree, mod_infos, loaded.entry_module_id);
    defer checked.deinit();
    if (checked.hasErrors()) {
        for (checked.diagnostics) |d| std.debug.print("stage I test 6 sema err: {s}\n", .{d.message});
    }
    try std.testing.expect(!checked.hasErrors());

    // L1d policy: SmallAuto (64 * 4 = 256 B <= 32 KiB) keeps hot_flag addressable (`bit_offset == null`),
    // while LargeAuto (16384 * 2 = 32 KiB+ / > 32 KiB) bitpacks hot_flag into a shared byte (`bit_offset != null`).
    var small_bit_off: ??u8 = null;
    var large_bit_off: ??u8 = null;
    for (checked.records) |r| {
        if (std.mem.eql(u8, r.name, "SmallAuto")) {
            for (r.fields, 0..) |cf, fi| if (std.mem.eql(u8, cf.name, "hot_flag")) {
                small_bit_off = r.record_layout.fields[fi].bit_offset;
            };
        } else if (std.mem.eql(u8, r.name, "LargeAuto")) {
            for (r.fields, 0..) |cf, fi| if (std.mem.eql(u8, cf.name, "hot_flag")) {
                large_bit_off = r.record_layout.fields[fi].bit_offset;
            };
        }
    }
    try std.testing.expect(small_bit_off != null and small_bit_off.? == null);
    try std.testing.expect(large_bit_off != null and large_bit_off.? != null);

    var zig_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer zig_buf.deinit();
    try codegen_zig.emitZig(&tree, &checked, &zig_buf.writer);
    const zig_src = zig_buf.written();
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "@select(") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "@Vector(8, u64)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "@reduce(.Add,") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "ensureExactCap(") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "aethelStrRepeat(") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "noalias __cb_") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__noalias_body") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__na_in_0") != null);

    var rust_lto_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer rust_lto_buf.deinit();
    try rust_ffi.emitCargoProjectAdapterWithOptions(
        &tree,
        &checked,
        "pub fn rust_step_cb(_q: BodySimd_px_vxQuery, _cb: impl Fn(&[f32]) -> f32) -> f32 { 0.0 }\n",
        "test_pkg",
        true,
        &rust_lto_buf.writer,
    );
    try std.testing.expect(std.mem.indexOf(u8, rust_lto_buf.written(), "#[inline(always)]\n    fn __aethel_soa_noalias_call<'a") != null);
}
