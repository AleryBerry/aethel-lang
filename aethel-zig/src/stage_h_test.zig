const std = @import("std");
const Io = std.Io;
const build_options = @import("build_options");
const ast = @import("ast.zig");
const parser = @import("parser.zig");
const manifest = @import("manifest.zig");
const module_loader = @import("module_loader.zig");
const sema = @import("sema.zig");
const codegen_zig = @import("codegen_zig.zig");
const rust_ffi = @import("rust_ffi.zig");

test "1. Stage H: aethel.toml manifest parsing, [dependencies] preservation, and add --rust" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const alloc = arena_state.allocator();

    const toml_src =
        \\# Aethel project manifest
        \\[package]
        \\name = "game_app"
        \\version = "0.2.0"
        \\entry = "src/main.aethel"
        \\
        \\[dependencies]
        \\future_native_pkg = "^0.1.0"
        \\
        \\[rust]
        \\edition = "2021"
        \\
        \\[rust-dependencies]
        \\serde = "1.0"
        \\bevy = { version = "0.17.3", default-features = false, features = ["bevy_state"] }
        \\
    ;

    const pm = try manifest.parseManifest(alloc, toml_src);
    try std.testing.expectEqualStrings("game_app", pm.pkg_name);
    try std.testing.expectEqualStrings("0.2.0", pm.pkg_version);
    try std.testing.expectEqualStrings("src/main.aethel", pm.entry);
    try std.testing.expectEqual(@as(usize, 1), pm.native_deps.len);
    try std.testing.expectEqualStrings("future_native_pkg", pm.native_deps[0].name);
    try std.testing.expectEqual(@as(usize, 2), pm.rust_deps.len);
    try std.testing.expectEqualStrings("bevy", pm.rust_deps[1].name);
    try std.testing.expectEqualStrings("0.17.3", pm.rust_deps[1].version.?);
    try std.testing.expect(!pm.rust_deps[1].default_features);
    try std.testing.expectEqual(@as(usize, 1), pm.rust_deps[1].features.len);
    try std.testing.expectEqualStrings("bevy_state", pm.rust_deps[1].features[0]);

    const parsed_spec = manifest.parseAddCrateSpec("rand@0.9.0");
    try std.testing.expectEqualStrings("rand", parsed_spec.name);
    try std.testing.expectEqualStrings("0.9.0", parsed_spec.version.?);

    const updated = try manifest.upsertRustDependency(alloc, &pm, .{
        .name = parsed_spec.name,
        .version = parsed_spec.version,
    });
    const rendered = try manifest.renderManifest(alloc, &updated);
    const reparsed = try manifest.parseManifest(alloc, rendered);
    try std.testing.expectEqual(@as(usize, 1), reparsed.native_deps.len);
    try std.testing.expectEqualStrings("future_native_pkg", reparsed.native_deps[0].name);
    try std.testing.expectEqual(@as(usize, 3), reparsed.rust_deps.len);
    try std.testing.expectEqualStrings("rand", reparsed.rust_deps[2].name);
}

test "2. Stage H: String (&str) and stateless Aethel -> Rust callback Zig & Rust FFI codegen" {
    const source: [:0]const u8 =
        \\@external(rust, "bevy_bridge", "register_greeter")
        \\pub fn register_greeter(prefix: String, cb: fn(String) -> ())
        \\
        \\@external(rust, "self", "map_u32")
        \\pub fn map_u32(x: u32, f: fn(u32) -> u32) -> u32
        \\
        \\pub fn my_greeter(name: String) {
        \\  println("hi ", name)
        \\}
        \\
        \\pub fn main() {
        \\  register_greeter("prefix", my_greeter)
        \\  let _ = map_u32(10u32, fn(v: u32) -> u32 { v +| 1u32 })
        \\}
    ;

    var tree = try parser.parse(std.testing.allocator, source);
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());

    const declared = [_][]const u8{"bevy_bridge"};
    var checked = try sema.analyzeWithModulesAndManifest(
        std.testing.allocator,
        &tree,
        &.{},
        0,
        "my_app",
        &declared,
    );
    defer checked.deinit();
    if (checked.hasErrors()) {
        for (checked.diagnostics) |d| std.debug.print("stage H test 2 sema err: {s}\n", .{d.message});
    }
    try std.testing.expect(!checked.hasErrors());

    var zig_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer zig_buf.deinit();
    try codegen_zig.emitZig(&tree, &checked, &zig_buf.writer);
    const zig_src = zig_buf.written();

    try std.testing.expect(std.mem.indexOf(u8, zig_src, "ext_bevy_bridge__register_greeter") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "prefix_ptr: [*]const u8, prefix_len: usize") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "cb_cb: *const fn (noalias [*]const u8, usize) callconv(.c) void") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__aethel_cb") != null);

    var rust_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer rust_buf.deinit();
    try rust_ffi.emitCargoProjectAdapter(&tree, &checked, null, "my_app", &rust_buf.writer);
    const rust_src = rust_buf.written();

    try std.testing.expect(std.mem.indexOf(u8, rust_src, "pub unsafe extern \"C\" fn ext_bevy_bridge__register_greeter(") != null);
    try std.testing.expect(std.mem.indexOf(u8, rust_src, "core::str::from_utf8(core::slice::from_raw_parts(prefix_ptr, prefix_len))") != null);
    try std.testing.expect(std.mem.indexOf(u8, rust_src, "cb_cb: unsafe extern \"C\" fn(*const u8, usize)") != null);
    try std.testing.expect(std.mem.indexOf(u8, rust_src, "::bevy_bridge::register_greeter(prefix, cb)") != null);
    try std.testing.expect(std.mem.indexOf(u8, rust_src, "aethel_rust_user::map_u32(x, f)") != null);
}

fn expectStageHSemaError(
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

test "3. Stage H: negative counterexamples (capturing callback, fn_once, String return, undeclared crate)" {
    // 1) Capturing local variable inside Aethel -> Rust callback rejected
    try expectStageHSemaError(
        \\@external(rust, "reg_cb")
        \\pub fn reg_cb(cb: fn(u32) -> u32)
        \\pub fn main() {
        \\  let bias: u32 = 5u32
        \\  reg_cb(fn(x: u32) -> u32 { x +| bias })
        \\}
    , null, null);

    // 2) once fn(...) callback rejected at FFI boundary
    try expectStageHSemaError(
        \\@external(rust, "reg_once")
        \\pub fn reg_once(cb: once fn(u32) -> u32)
        \\pub fn main() {}
    , null, null);

    // 3) Returning borrowed String (&str) directly from Rust FFI rejected
    try expectStageHSemaError(
        \\@external(rust, "bad_ret")
        \\pub fn bad_ret() -> String
        \\pub fn main() {}
    , null, null);

    // 4) Undeclared Cargo crate target in @external(rust, crate, sym) rejected
    const declared = [_][]const u8{"bevy"};
    try expectStageHSemaError(
        \\@external(rust, "tokio", "sleep_ms")
        \\pub fn sleep_ms(ms: u32)
        \\pub fn main() {}
    , "my_app", &declared);
}

test "4. Stage H: end-to-end local Cargo crate + String & retained Aethel callback execution" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const io = std.testing.io;

    const proj_root = ".aethel-build/test_stage_h_proj";
    defer Io.Dir.cwd().deleteTree(io, proj_root) catch {};

    try Io.Dir.cwd().createDirPath(io, ".aethel-build/test_stage_h_proj/crate_a/src");
    try Io.Dir.cwd().createDirPath(io, ".aethel-build/test_stage_h_proj/rust/src");
    try Io.Dir.cwd().createDirPath(io, ".aethel-build/test_stage_h_proj/src");

    try Io.Dir.cwd().writeFile(io, .{
        .sub_path = ".aethel-build/test_stage_h_proj/crate_a/Cargo.toml",
        .data =
        \\[package]
        \\name = "greeter-core"
        \\version = "0.1.0"
        \\edition = "2021"
        \\
        ,
    });
    try Io.Dir.cwd().writeFile(io, .{
        .sub_path = ".aethel-build/test_stage_h_proj/crate_a/src/lib.rs",
        .data =
        \\pub fn drive_callback(label: &str, cb: impl Fn(&str, u32) -> u32 + Send + Sync + 'static) -> u32 {
        \\    cb(label, 40)
        \\}
        \\
        ,
    });
    try Io.Dir.cwd().writeFile(io, .{
        .sub_path = ".aethel-build/test_stage_h_proj/rust/src/lib.rs",
        .data =
        \\pub fn run_retained(label: &str, cb: impl Fn(&str, u32) -> u32 + Send + Sync + 'static) -> u32 {
        \\    ::greeter_core::drive_callback(label, cb)
        \\}
        \\
        ,
    });

    const aethel_src: [:0]const u8 =
        \\@external(rust, "self", "run_retained")
        \\pub fn run_retained(label: String, cb: fn(String, u32) -> u32) -> u32
        \\
        \\pub fn on_event(msg: String, base: u32) -> u32 {
        \\  println("cb:", msg)
        \\  base +| 2u32
        \\}
        \\
        \\pub fn main() {
        \\  let total = run_retained("aethel_cargo_ok", on_event)
        \\  println("total=", total)
        \\}
    ;

    const pm = manifest.ProjectManifest{
        .pkg_name = "stage_h_e2e",
        .rust_deps = &.{.{
            .name = "greeter-core",
            .path = "crate_a",
        }},
    };

    var tree = try parser.parse(arena, aethel_src);
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());

    const declared = [_][]const u8{"greeter-core"};
    var checked = try sema.analyzeWithModulesAndManifest(arena, &tree, &.{}, 0, pm.pkg_name, &declared);
    defer checked.deinit();
    try std.testing.expect(!checked.hasErrors());

    var stderr_buf: Io.Writer.Allocating = .init(arena);
    const cargo_out_opt = try rust_ffi.compileCargoProjectStaticlib(
        io,
        arena,
        &tree,
        &checked,
        proj_root,
        &pm,
        ".aethel-build/test_stage_h_proj/rust/src/lib.rs",
        false,
        true,
        &stderr_buf.writer,
    );
    if (cargo_out_opt == null) {
        std.debug.print("compileCargoProjectStaticlib stderr:\n{s}\n", .{stderr_buf.written()});
    }
    try std.testing.expect(cargo_out_opt != null);
    const cargo_out = cargo_out_opt.?;

    var zig_buf: Io.Writer.Allocating = .init(arena);
    try codegen_zig.emitZig(&tree, &checked, &zig_buf.writer);
    const zig_path = ".aethel-build/test_stage_h_proj/out.zig";
    const bin_path = ".aethel-build/test_stage_h_proj/out_bin";
    try Io.Dir.cwd().writeFile(io, .{ .sub_path = zig_path, .data = zig_buf.written() });

    const emit_bin = try std.fmt.allocPrint(arena, "-femit-bin={s}", .{bin_path});
    var argv: std.ArrayList([]const u8) = .empty;
    try argv.appendSlice(arena, &.{
        build_options.zig_exe,
        "build-exe",
        zig_path,
        "-fno-llvm",
        "-fno-lld",
        cargo_out.staticlib_path,
    });
    for (cargo_out.link_flags) |lf| try argv.append(arena, lf);
    try argv.appendSlice(arena, &.{ emit_bin, "--cache-dir", ".aethel-build/cache" });

    var bres = try std.process.run(arena, io, .{ .argv = argv.items });
    if (!bres.term.success()) {
        // Retry without -fno-lld
        var argv2: std.ArrayList([]const u8) = .empty;
        for (argv.items) |a| {
            if (!std.mem.eql(u8, a, "-fno-lld")) try argv2.append(arena, a);
        }
        bres = try std.process.run(arena, io, .{ .argv = argv2.items });
    }
    if (!bres.term.success()) {
        std.debug.print("zig build-exe stderr:\n{s}\n", .{bres.stderr});
    }
    try std.testing.expect(bres.term.success());

    const run_res = try std.process.run(arena, io, .{ .argv = &.{"./.aethel-build/test_stage_h_proj/out_bin"} });
    try std.testing.expect(run_res.term.success());
    try std.testing.expect(std.mem.indexOf(u8, run_res.stdout, "cb:aethel_cargo_ok") != null);
    try std.testing.expect(std.mem.indexOf(u8, run_res.stdout, "total=42") != null);
}
