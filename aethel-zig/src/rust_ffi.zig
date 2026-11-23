const std = @import("std");
const Io = std.Io;
const ast = @import("ast.zig");
const sema = @import("sema.zig");

/// Generate a synchronous Rust C-ABI adapter module backed by `Aethel/RustFFI.lean`.
/// For every `extern "rust" fn` whose symbol is not already exported with `extern "C"`
/// in `user_rust_source`, generates a `#[no_mangle] pub unsafe extern "C" fn` shim that
/// validates and constructs safe `&[T]` / `&mut [T]` slices (or opaque pointers) and
/// delegates to `aethel_rust_user::<name>(...)`.
pub fn emitRustAdapter(
    tree: *const ast.Ast,
    checked: *const sema.CheckedModule,
    user_rust_source: ?[]const u8,
    writer: *Io.Writer,
) Io.Writer.Error!void {
    try writer.writeAll("// Auto-generated Aethel -> Rust C-ABI adapter (verified against Aethel/RustFFI.lean)\n");

    var rust_fns_buf: [128]struct {
        ef: ast.ExternFn,
        fname: []const u8,
        cf: ?*const sema.CheckedFunction,
    } = undefined;
    var rust_fns_len: usize = 0;

    for (tree.module.decls) |decl| {
        if (decl.kind != .extern_decl) continue;
        const ex = decl.kind.extern_decl;
        const abi = ex.abi.slice(tree.source);
        if (!std.mem.eql(u8, abi, "\"rust\"")) continue;
        for (ex.fns) |ef| {
            if (rust_fns_len >= rust_fns_buf.len) break;
            const fname = ef.name.slice(tree.source);
            var matched_cf: ?*const sema.CheckedFunction = null;
            for (checked.functions) |*f| {
                if (f.has_extern_abi and std.mem.eql(u8, f.name, fname)) {
                    matched_cf = f;
                    break;
                }
            }
            rust_fns_buf[rust_fns_len] = .{
                .ef = ef,
                .fname = fname,
                .cf = matched_cf,
            };
            rust_fns_len += 1;
        }
    }

    const rust_fns = rust_fns_buf[0..rust_fns_len];

    var any_needs_shim = false;
    for (rust_fns) |rf| {
        if (user_rust_source == null or !hasExplicitExternCExport(user_rust_source.?, rf.fname)) {
            any_needs_shim = true;
            break;
        }
    }

    if (user_rust_source) |user_src| {
        if (!any_needs_shim) {
            try writer.writeAll(user_src);
            if (user_src.len > 0 and user_src[user_src.len - 1] != '\n') {
                try writer.writeByte('\n');
            }
            return;
        }
        // Hoist crate-level `#![...]` attributes before opening `mod aethel_rust_user`.
        var line_it = std.mem.splitScalar(u8, user_src, '\n');
        while (line_it.next()) |line| {
            const trimmed = std.mem.trimStart(u8, line, " \t\r");
            if (std.mem.startsWith(u8, trimmed, "#![")) {
                try writer.writeAll(line);
                try writer.writeByte('\n');
            }
        }
        try writer.writeAll("\n#[allow(dead_code, unused_imports)]\nmod aethel_rust_user {\n");
        var body_it = std.mem.splitScalar(u8, user_src, '\n');
        while (body_it.next()) |line| {
            const trimmed = std.mem.trimStart(u8, line, " \t\r");
            if (std.mem.startsWith(u8, trimmed, "#![")) continue;
            if (line.len > 0) try writer.writeAll("    ");
            try writer.writeAll(line);
            try writer.writeByte('\n');
        }
        try writer.writeAll("}\n\n");
    }

    for (rust_fns) |rf| {
        if (user_rust_source != null and hasExplicitExternCExport(user_rust_source.?, rf.fname)) {
            continue;
        }
        try emitExternCShim(tree.source, rf.ef, rf.fname, rf.cf, writer);
        try writer.writeByte('\n');
    }
}

fn emitExternCShim(
    source: [:0]const u8,
    ef: ast.ExternFn,
    fname: []const u8,
    cf: ?*const sema.CheckedFunction,
    writer: *Io.Writer,
) Io.Writer.Error!void {
    try writer.print("#[no_mangle]\npub unsafe extern \"C\" fn {s}(\n", .{fname});
    for (ef.params, 0..) |p, pi| {
        const pname = p.name.slice(source);
        const pty: ?*const sema.Ty = if (cf != null and pi < cf.?.param_types.len) cf.?.param_types[pi] else null;
        if (pty != null and isSliceTy(pty.?)) {
            const sl = unwrapSliceTy(pty.?);
            const qual = if (sl.mutable) "*mut " else "*const ";
            try writer.print("    {s}_ptr: {s}", .{ pname, qual });
            try emitRustScalarTy(sl.elem, writer);
            try writer.print(",\n    {s}_len: usize,\n", .{pname});
        } else if (p.ty != null and p.ty.?.* == .slice) {
            const sl = p.ty.?.slice;
            const qual = if (sl.mutable) "*mut " else "*const ";
            try writer.print("    {s}_ptr: {s}", .{ pname, qual });
            try emitRustAstTy(source, sl.elem, writer);
            try writer.print(",\n    {s}_len: usize,\n", .{pname});
        } else {
            try writer.print("    {s}: ", .{pname});
            if (pty) |t| {
                try emitRustABITy(t, writer);
            } else if (p.ty) |at| {
                try emitRustAstTy(source, at, writer);
            } else {
                try writer.writeAll("usize");
            }
            try writer.writeAll(",\n");
        }
    }
    try writer.writeByte(')');
    const ret_ty: ?*const sema.Ty = if (cf) |f| f.ret_type else null;
    if (ret_ty != null and ret_ty.?.* != .unit and ret_ty.?.* != .err) {
        try writer.writeAll(" -> ");
        try emitRustABITy(ret_ty.?, writer);
    } else if (ef.ret) |rt| {
        try writer.writeAll(" -> ");
        try emitRustAstTy(source, rt, writer);
    }
    try writer.writeAll(" {\n");

    for (ef.params, 0..) |p, pi| {
        const pname = p.name.slice(source);
        const pty: ?*const sema.Ty = if (cf != null and pi < cf.?.param_types.len) cf.?.param_types[pi] else null;
        if (pty != null and isSliceTy(pty.?)) {
            const sl = unwrapSliceTy(pty.?);
            const slice_ref = if (sl.mutable) "&mut [" else "&[";
            const empty_expr = if (sl.mutable) "&mut []" else "&[]";
            const raw_fn = if (sl.mutable) "from_raw_parts_mut" else "from_raw_parts";
            try writer.print("    let {s}: {s}", .{ pname, slice_ref });
            try emitRustScalarTy(sl.elem, writer);
            try writer.print("] = if {s}_len == 0 {{ {s} }} else {{ core::slice::{s}({s}_ptr, {s}_len) }};\n", .{
                pname,
                empty_expr,
                raw_fn,
                pname,
                pname,
            });
        } else if (p.ty != null and p.ty.?.* == .slice) {
            const sl = p.ty.?.slice;
            const slice_ref = if (sl.mutable) "&mut [" else "&[";
            const empty_expr = if (sl.mutable) "&mut []" else "&[]";
            const raw_fn = if (sl.mutable) "from_raw_parts_mut" else "from_raw_parts";
            try writer.print("    let {s}: {s}", .{ pname, slice_ref });
            try emitRustAstTy(source, sl.elem, writer);
            try writer.print("] = if {s}_len == 0 {{ {s} }} else {{ core::slice::{s}({s}_ptr, {s}_len) }};\n", .{
                pname,
                empty_expr,
                raw_fn,
                pname,
                pname,
            });
        }
    }

    try writer.print("    aethel_rust_user::{s}(", .{fname});
    for (ef.params, 0..) |p, pi| {
        if (pi > 0) try writer.writeAll(", ");
        try writer.writeAll(p.name.slice(source));
    }
    try writer.writeAll(")\n}\n");
}

fn isSliceTy(ty: *const sema.Ty) bool {
    return switch (ty.*) {
        .slice => true,
        .view => |v| v.target.* == .slice,
        else => false,
    };
}

fn unwrapSliceTy(ty: *const sema.Ty) struct { mutable: bool, elem: *const sema.Ty } {
    return switch (ty.*) {
        .slice => |s| .{ .mutable = s.mutable, .elem = s.elem },
        .view => |v| .{
            .mutable = v.mode == .exclusive and v.target.slice.mutable,
            .elem = v.target.slice.elem,
        },
        else => unreachable,
    };
}

fn emitRustScalarTy(ty: *const sema.Ty, writer: *Io.Writer) Io.Writer.Error!void {
    switch (ty.*) {
        .int => |it| try writer.print("{c}{d}", .{ if (it.signed) @as(u8, 'i') else @as(u8, 'u'), it.bits }),
        .int_range => |ir| try writer.print("{c}{d}", .{
            if (ir.synthesized.signed) @as(u8, 'i') else @as(u8, 'u'),
            ir.synthesized.bits,
        }),
        .f32 => try writer.writeAll("f32"),
        .f64 => try writer.writeAll("f64"),
        .bool => try writer.writeAll("bool"),
        .unit => try writer.writeAll("()"),
        else => try writer.writeAll("u8"),
    }
}

fn emitRustABITy(ty: *const sema.Ty, writer: *Io.Writer) Io.Writer.Error!void {
    switch (ty.*) {
        .opaque_ty => try writer.writeAll("*mut core::ffi::c_void"),
        .view => |v| {
            if (v.target.* == .opaque_ty) {
                if (v.mode == .shared) {
                    try writer.writeAll("*const core::ffi::c_void");
                } else {
                    try writer.writeAll("*mut core::ffi::c_void");
                }
            } else {
                try emitRustScalarTy(ty, writer);
            }
        },
        else => try emitRustScalarTy(ty, writer),
    }
}

fn emitRustAstTy(source: [:0]const u8, ty_ast: *const ast.TypeExpr, writer: *Io.Writer) Io.Writer.Error!void {
    switch (ty_ast.*) {
        .primitive => |p| switch (p.prim) {
            .unsigned => |bits| try writer.print("u{d}", .{bits}),
            .signed => |bits| try writer.print("i{d}", .{bits}),
            .f32 => try writer.writeAll("f32"),
            .f64 => try writer.writeAll("f64"),
            .bool => try writer.writeAll("bool"),
        },
        .named => |n| {
            if (n.path.len > 0 and std.mem.eql(u8, n.path[n.path.len - 1].slice(source), "View") and n.args.len >= 2) {
                const is_shared = n.args[1].* == .named and n.args[1].named.path.len > 0 and
                    std.mem.eql(u8, n.args[1].named.path[0].slice(source), "Shared");
                try writer.writeAll(if (is_shared) "*const core::ffi::c_void" else "*mut core::ffi::c_void");
            } else {
                try writer.writeAll("*mut core::ffi::c_void");
            }
        },
        else => try writer.writeAll("*mut core::ffi::c_void"),
    }
}

/// Detect whether `src` already defines an `extern "C" fn <name>(` (or `"c"`).
pub fn hasExplicitExternCExport(src: []const u8, name: []const u8) bool {
    var i: usize = 0;
    while (i + 6 < src.len) : (i += 1) {
        if (!std.mem.startsWith(u8, src[i..], "extern")) continue;
        if (i > 0 and isIdentChar(src[i - 1])) continue;
        var j = i + 6;
        if (j >= src.len or !isWs(src[j])) continue;
        while (j < src.len and isWs(src[j])) : (j += 1) {}
        if (j + 3 > src.len or src[j] != '"' or (src[j + 1] != 'C' and src[j + 1] != 'c') or src[j + 2] != '"') {
            continue;
        }
        j += 3;
        while (j < src.len and isWs(src[j])) : (j += 1) {}
        if (!std.mem.startsWith(u8, src[j..], "fn")) continue;
        j += 2;
        if (j >= src.len or !isWs(src[j])) continue;
        while (j < src.len and isWs(src[j])) : (j += 1) {}
        if (!std.mem.startsWith(u8, src[j..], name)) continue;
        j += name.len;
        while (j < src.len and isWs(src[j])) : (j += 1) {}
        if (j < src.len and src[j] == '(') return true;
    }
    return false;
}

fn isWs(c: u8) bool {
    return c == ' ' or c == '\t' or c == '\n' or c == '\r';
}

fn isIdentChar(c: u8) bool {
    return (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or (c >= '0' and c <= '9') or c == '_';
}

/// Generate the adapter Rust file inside `.aethel-build/` and compile it with `rustc`
/// into a C-ABI `.a` static library ready for Zig's built-in linker (`-fno-llvm -fno-lld`).
pub fn compileRustStaticlib(
    io: Io,
    arena: std.mem.Allocator,
    tree: *const ast.Ast,
    checked: *const sema.CheckedModule,
    rust_path: []const u8,
    stem: []const u8,
    stderr: *Io.Writer,
) !?[]const u8 {
    const user_rust_src = Io.Dir.cwd().readFileAllocOptions(
        io,
        rust_path,
        arena,
        .limited(16 * 1024 * 1024),
        .of(u8),
        0,
    ) catch |err| {
        try stderr.print("error: failed to read Rust source '{s}': {s}\n", .{ rust_path, @errorName(err) });
        try stderr.flush();
        return null;
    };

    var bridge_buf: Io.Writer.Allocating = .init(arena);
    try emitRustAdapter(tree, checked, user_rust_src, &bridge_buf.writer);

    const bridge_path = try std.fmt.allocPrint(arena, ".aethel-build/{s}_rust_bridge.rs", .{stem});
    const lib_path = try std.fmt.allocPrint(arena, ".aethel-build/lib{s}_rust.a", .{stem});

    Io.Dir.cwd().writeFile(io, .{ .sub_path = bridge_path, .data = bridge_buf.written() }) catch |err| {
        try stderr.print("error: failed to write Rust adapter '{s}': {s}\n", .{ bridge_path, @errorName(err) });
        try stderr.flush();
        return null;
    };

    const rustc_candidates = [_][]const u8{ "rustc", "/sbin/rustc" };
    var rustc_res_opt: ?std.process.RunResult = null;
    for (rustc_candidates) |rc_bin| {
        if (std.process.run(arena, io, .{
            .argv = &.{
                rc_bin,
                "--edition",
                "2021",
                "--crate-type",
                "staticlib",
                "-C",
                "panic=abort",
                "-O",
                "-o",
                lib_path,
                bridge_path,
            },
        })) |res| {
            rustc_res_opt = res;
            break;
        } else |err| {
            if (err == error.FileNotFound) continue;
            try stderr.print("error: failed to invoke '{s}': {s}\n", .{ rc_bin, @errorName(err) });
            try stderr.flush();
            return null;
        }
    }

    const rustc_res = rustc_res_opt orelse {
        try stderr.print("error: 'rustc' compiler not found in PATH or /sbin/rustc\n", .{});
        try stderr.flush();
        return null;
    };

    if (!rustc_res.term.success()) {
        try stderr.print("error: rustc failed to compile '{s}' ({f}):\n{s}\n", .{
            rust_path,
            rustc_res.term,
            rustc_res.stderr,
        });
        try stderr.flush();
        return null;
    }

    return lib_path;
}
