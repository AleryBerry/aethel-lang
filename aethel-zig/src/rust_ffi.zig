const std = @import("std");
const Io = std.Io;
const ast = @import("ast.zig");
const sema = @import("sema.zig");
const manifest = @import("manifest.zig");

const RustFFIEntry = struct {
    sym_name: []const u8,
    call_path: []const u8,
    is_external_crate_call: bool = false,
    param_names: []const []const u8,
    param_types: []const *const sema.Ty,
    ret_type: *const sema.Ty,
    ast_extern: ?ast.ExternFn = null,
};

const SoaQuerySpec = struct {
    struct_name: []const u8,
    ridx: usize,
    field_indices: []const usize,
    is_mut: bool,
};

const AoSoASpec = struct {
    tile_name: []const u8,
    view_name: []const u8,
    ridx: usize,
    width: usize,
    is_mut: bool,
};

/// Generate a synchronous Rust C-ABI adapter module backed by `Aethel/RustFFI.lean`,
/// `Aethel/RustBorrowBridge.lean`, `Aethel/RustTraitBridge.lean`, and `Aethel/RustComplexABI.lean`.
/// Supports legacy `extern "rust"`, `@external(rust, ...)` functions/instances, `#[repr(C)]` flat
/// structs, Bevy-style SoA split-column queries, 64B-aligned AoSoA tile slices, and Cargo crates.
pub fn emitRustAdapter(
    tree: *const ast.Ast,
    checked: *const sema.CheckedModule,
    user_rust_source: ?[]const u8,
    writer: *Io.Writer,
) Io.Writer.Error!void {
    return emitRustAdapterInner(tree, checked, user_rust_source, null, null, false, writer);
}

pub fn emitCargoProjectAdapter(
    tree: *const ast.Ast,
    checked: *const sema.CheckedModule,
    user_rust_source: ?[]const u8,
    project_pkg_name: ?[]const u8,
    writer: *Io.Writer,
) Io.Writer.Error!void {
    return emitRustAdapterInner(tree, checked, user_rust_source, null, project_pkg_name, false, writer);
}

pub fn emitCargoProjectAdapterWithOptions(
    tree: *const ast.Ast,
    checked: *const sema.CheckedModule,
    user_rust_source: ?[]const u8,
    project_pkg_name: ?[]const u8,
    use_cross_lto: bool,
    writer: *Io.Writer,
) Io.Writer.Error!void {
    return emitRustAdapterInner(tree, checked, user_rust_source, null, project_pkg_name, use_cross_lto, writer);
}

fn emitRustAdapterInner(
    tree: *const ast.Ast,
    checked: *const sema.CheckedModule,
    user_rust_source: ?[]const u8,
    cargo_crate_ident: ?[]const u8,
    project_pkg_name: ?[]const u8,
    use_cross_lto: bool,
    writer: *Io.Writer,
) Io.Writer.Error!void {
    try writer.writeAll("// Auto-generated Aethel -> Rust C-ABI adapter (verified against Aethel Rust Bridge proofs)\n");

    var entries: [256]RustFFIEntry = undefined;
    var entries_len: usize = 0;

    var dyn_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer dyn_arena.deinit();
    const alloc = dyn_arena.allocator();

    // 1. Legacy `extern "rust"` blocks.
    for (tree.module.decls) |decl| {
        if (decl.kind != .extern_decl) continue;
        const ex = decl.kind.extern_decl;
        if (!std.mem.eql(u8, ex.abi.slice(tree.source), "\"rust\"")) continue;
        for (ex.fns) |ef| {
            if (entries_len >= entries.len) break;
            const fname = ef.name.slice(tree.source);
            var matched_cf: ?*const sema.CheckedFunction = null;
            for (checked.functions) |*f| {
                if (f.has_extern_abi and std.mem.eql(u8, f.name, fname)) {
                    matched_cf = f;
                    break;
                }
            }
            const pnames = alloc.alloc([]const u8, ef.params.len) catch continue;
            for (ef.params, 0..) |p, pi| pnames[pi] = p.name.slice(tree.source);
            entries[entries_len] = .{
                .sym_name = fname,
                .call_path = fname,
                .param_names = pnames,
                .param_types = if (matched_cf) |cf| cf.param_types else &.{},
                .ret_type = if (matched_cf) |cf| cf.ret_type else &.{ .unit = {} },
                .ast_extern = ef,
            };
            entries_len += 1;
        }
    }

    // 2. Gleam-style `@external(rust, ...)` functions.

    for (tree.module.decls) |decl| {
        if (decl.kind != .fn_decl) continue;
        const fd = decl.kind.fn_decl;
        if (fd.has_body) continue;
        if (entries_len >= entries.len) break;
        const local_name = fd.name.slice(tree.source);
        const cname = checked.declCanonicalName(decl.span.start) orelse local_name;
        var matched_cf: ?*const sema.CheckedFunction = null;
        for (checked.functions) |*f| {
            if (f.has_extern_abi and std.mem.eql(u8, f.name, cname)) {
                matched_cf = f;
                break;
            }
        }
        const cf = matched_cf orelse continue;
        const sym = cf.rust_sym orelse cname;
        var call_path = sym;
        var is_ext_crate = false;
        for (checked.foreign_contracts) |fc| {
            if (std.mem.eql(u8, fc.aethel_name, cname)) {
                call_path = fc.rust_sym;
                if (fc.rust_target) |tgt| {
                    const is_local = std.mem.eql(u8, tgt, "self") or
                        std.mem.eql(u8, tgt, "bridge") or
                        (project_pkg_name != null and manifest.cratesMatch(tgt, project_pkg_name.?)) or
                        (cargo_crate_ident != null and manifest.cratesMatch(tgt, cargo_crate_ident.?));
                    if (is_local) {
                        call_path = fc.rust_sym;
                    } else if (project_pkg_name != null) {
                        const norm_tgt = manifest.normalizeCrateIdentAlloc(alloc, tgt) catch tgt;
                        call_path = std.fmt.allocPrint(alloc, "::{s}::{s}", .{ norm_tgt, fc.rust_sym }) catch fc.rust_sym;
                        is_ext_crate = true;
                    } else {
                        call_path = std.fmt.allocPrint(alloc, "{s}::{s}", .{ tgt, fc.rust_sym }) catch fc.rust_sym;
                    }
                }
                break;
            }
        }
        const pnames = alloc.alloc([]const u8, fd.params.len) catch continue;
        for (fd.params, 0..) |p, pi| pnames[pi] = p.name.slice(tree.source);
        entries[entries_len] = .{
            .sym_name = sym,
            .call_path = call_path,
            .is_external_crate_call = is_ext_crate,
            .param_names = pnames,
            .param_types = cf.param_types,
            .ret_type = cf.ret_type,
        };
        entries_len += 1;
    }

    // 3. `@external(rust, ...)` trait instances.
    for (checked.instances) |inst| {
        if (!inst.is_external_rust) continue;
        for (inst.methods) |cm| {
            if (entries_len >= entries.len) break;
            const esym = cm.ext_sym orelse continue;
            const call_target = if (inst.rust_target) |rt|
                (std.fmt.allocPrint(alloc, "{s}::{s}", .{ rt, cm.local_name }) catch cm.local_name)
            else if (inst.rust_sym) |rs|
                (std.fmt.allocPrint(alloc, "{s}::{s}", .{ rs, cm.local_name }) catch cm.local_name)
            else
                cm.local_name;
            const pnames = alloc.alloc([]const u8, cm.params.len) catch continue;
            for (0..cm.params.len) |pi| {
                pnames[pi] = if (cm.ast_method != null and pi < cm.ast_method.?.params.len)
                    cm.ast_method.?.params[pi].name.slice(tree.source)
                else
                    (std.fmt.allocPrint(alloc, "arg{d}", .{pi}) catch "arg");
            }
            entries[entries_len] = .{
                .sym_name = esym,
                .call_path = call_target,
                .param_names = pnames,
                .param_types = cm.params,
                .ret_type = cm.ret,
            };
            entries_len += 1;
        }
    }

    const active_entries = entries[0..entries_len];
    var any_needs_shim = false;
    for (active_entries) |ent| {
        if (user_rust_source == null or !hasExplicitExternCExport(user_rust_source.?, ent.sym_name)) {
            any_needs_shim = true;
            break;
        }
    }

    // Collect SoA / AoSoA wrapper structs needed by FFI entries.
    var soa_specs: std.ArrayList(SoaQuerySpec) = .empty;
    var aosoa_specs: std.ArrayList(AoSoASpec) = .empty;
    for (active_entries) |ent| {
        for (ent.param_types) |pt| {
            collectSoAAoSoASpecs(alloc, tree.source, checked, pt, &soa_specs, &aosoa_specs) catch {};
        }
    }

    // Emit shared C-ABI #[repr(C)] mirror structs, SoA queries, and AoSoA tiles before `mod aethel_rust_user`.
    var emitted_header = false;
    for (checked.records) |rec| {
        if (!rec.is_flat_c) continue;
        if (cargo_crate_ident == null and user_rust_source != null and hasRustStructDef(user_rust_source.?, rec.name)) continue;
        if (!emitted_header) {
            try writer.writeAll("\n// Verified flat C-ABI mirror structs (RustComplexABI.lean / ProcMacroInterop.lean)\n");
            emitted_header = true;
        }
        try writer.writeAll("#[repr(C)]\n#[derive(Copy, Clone, Debug");
        for (rec.rust_derives) |raw_drv| {
            if (std.mem.eql(u8, raw_drv, "Copy") or std.mem.eql(u8, raw_drv, "Clone") or std.mem.eql(u8, raw_drv, "Debug")) {
                continue;
            }
            if (std.mem.indexOf(u8, raw_drv, "::") != null and !std.mem.startsWith(u8, raw_drv, "::")) {
                try writer.print(", ::{s}", .{raw_drv});
            } else {
                try writer.print(", {s}", .{raw_drv});
            }
        }
        try writer.writeAll(")]\n");
        for (rec.rust_attrs) |ra| {
            try writer.print("#[{s}]\n", .{ra});
        }
        try writer.print("pub struct {s} {{\n", .{rec.name});
        for (rec.fields) |f| {
            for (f.rust_attrs) |fa| {
                try writer.print("    #[{s}]\n", .{fa});
            }
            try writer.print("    pub {s}: ", .{f.name});
            try emitRustABITy(checked, f.ty, writer);
            try writer.writeAll(",\n");
        }
        try writer.writeAll("}\n");
    }

    for (soa_specs.items) |qs| {
        const rec = checked.records[qs.ridx];
        try writer.print("\n#[allow(dead_code)]\npub struct {s}<'a> {{\n", .{qs.struct_name});
        const ref_pre = if (qs.is_mut) "&'a mut [" else "&'a [";
        for (qs.field_indices) |fi| {
            const f = rec.fields[fi];
            try writer.print("    pub {s}: {s}", .{ f.name, ref_pre });
            try emitRustABITy(checked, f.ty, writer);
            try writer.writeAll("],\n");
        }
        try writer.writeAll("    pub len: usize,\n}\n");
    }

    var emitted_tiles = std.StringHashMapUnmanaged(void).empty;
    for (aosoa_specs.items) |as| {
        const rec = checked.records[as.ridx];
        if (!emitted_tiles.contains(as.tile_name)) {
            emitted_tiles.put(alloc, as.tile_name, {}) catch {};
            try writer.print("\n#[repr(C, align(64))]\n#[derive(Copy, Clone, Debug)]\npub struct {s} {{\n", .{as.tile_name});
            for (rec.fields) |f| {
                try writer.print("    pub {s}: [", .{f.name});
                try emitRustABITy(checked, f.ty, writer);
                try writer.print("; {d}],\n", .{as.width});
            }
            try writer.writeAll("}\n");
        }
        const ref_pre = if (as.is_mut) "&'a mut [" else "&'a [";
        try writer.print("\n#[allow(dead_code)]\npub struct {s}<'a> {{\n", .{as.view_name});
        try writer.print("    pub tiles: {s}{s}],\n", .{ ref_pre, as.tile_name });
        try writer.writeAll("    pub base_elem: usize,\n    pub len: usize,\n}\n");
    }

    if (cargo_crate_ident) |cid| {
        try writer.print("\nextern crate {s} as aethel_rust_user;\n\n", .{cid});
    } else if (user_rust_source) |user_src| {
        if (!any_needs_shim) {
            try writer.writeAll(user_src);
            if (user_src.len > 0 and user_src[user_src.len - 1] != '\n') {
                try writer.writeByte('\n');
            }
            return;
        }
        var line_it = std.mem.splitScalar(u8, user_src, '\n');
        while (line_it.next()) |line| {
            const trimmed = std.mem.trimStart(u8, line, " \t\r");
            if (std.mem.startsWith(u8, trimmed, "#![")) {
                try writer.writeAll(line);
                try writer.writeByte('\n');
            }
        }
        try writer.writeAll("\n#[allow(dead_code, unused_imports)]\nmod aethel_rust_user {\n");
        try writer.writeAll("    #[allow(unused_imports)]\n    use super::*;\n");
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

    for (active_entries) |ent| {
        if (user_rust_source != null and hasExplicitExternCExport(user_rust_source.?, ent.sym_name)) {
            continue;
        }
        try emitExternCShimEntry(alloc, tree.source, checked, ent, cargo_crate_ident != null, use_cross_lto, writer);
        try writer.writeByte('\n');
    }
}

fn collectionBackingRecord(checked: *const sema.CheckedModule, pt: *const sema.Ty) ?struct {
    ridx: usize,
    layout: sema.CheckedCollection,
    is_mut: bool,
} {
    const inner: *const sema.Ty = switch (pt.*) {
        .view => |v| v.target,
        .path_borrow => |pb| pb.base,
        else => pt,
    };
    if (inner.* != .collection) return null;
    const ridx = inner.collection.elem_record orelse return null;
    if (ridx >= checked.records.len) return null;
    const rec = checked.records[ridx];
    const cl = rec.collection_layout orelse return null;
    const is_mut = switch (pt.*) {
        .view => |v| v.mode == .exclusive,
        .path_borrow => |pb| pb.mode == null or pb.mode.? == .exclusive,
        .collection => true,
        else => false,
    };
    if (cl == .aos) return null;
    return .{
        .ridx = ridx,
        .layout = .{ .name = rec.name, .layout = cl, .field_count = rec.fields.len },
        .is_mut = is_mut,
    };
}

fn collectFieldIndices(alloc: std.mem.Allocator, source: [:0]const u8, rec: sema.CheckedRecord, pt: *const sema.Ty) []const usize {
    var list: std.ArrayList(usize) = .empty;
    if (pt.* == .path_borrow) {
        for (pt.path_borrow.paths) |fp| {
            if (fp.len == 0) continue;
            const fnm = fp[0].slice(source);
            for (rec.fields, 0..) |f, fi| {
                if (std.mem.eql(u8, f.name, fnm)) {
                    var dup = false;
                    for (list.items) |prev| if (prev == fi) {
                        dup = true;
                    };
                    if (!dup) list.append(alloc, fi) catch {};
                    break;
                }
            }
        }
    }
    if (list.items.len == 0) {
        for (0..rec.fields.len) |fi| list.append(alloc, fi) catch {};
    }
    return list.toOwnedSlice(alloc) catch &.{};
}

fn makeSoaQueryName(alloc: std.mem.Allocator, rec: sema.CheckedRecord, fidxs: []const usize, is_mut: bool) []const u8 {
    if (fidxs.len == rec.fields.len) {
        return std.fmt.allocPrint(alloc, "{s}{s}Query", .{ rec.name, if (is_mut) "" else "Ref" }) catch rec.name;
    }
    var buf: std.ArrayList(u8) = .empty;
    buf.appendSlice(alloc, rec.name) catch {};
    for (fidxs) |fi| {
        buf.append(alloc, '_') catch {};
        buf.appendSlice(alloc, rec.fields[fi].name) catch {};
    }
    if (!is_mut) buf.appendSlice(alloc, "Ref") catch {};
    buf.appendSlice(alloc, "Query") catch {};
    return buf.toOwnedSlice(alloc) catch rec.name;
}

fn collectSoAAoSoASpecs(
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    checked: *const sema.CheckedModule,
    pt: *const sema.Ty,
    soa_out: *std.ArrayList(SoaQuerySpec),
    aosoa_out: *std.ArrayList(AoSoASpec),
) !void {
    const col = collectionBackingRecord(checked, pt) orelse return;
    const rec = checked.records[col.ridx];
    switch (col.layout.layout) {
        .soa => {
            const fidxs = collectFieldIndices(alloc, source, rec, pt);
            const qname = makeSoaQueryName(alloc, rec, fidxs, col.is_mut);
            for (soa_out.items) |prev| {
                if (std.mem.eql(u8, prev.struct_name, qname)) return;
            }
            try soa_out.append(alloc, .{
                .struct_name = qname,
                .ridx = col.ridx,
                .field_indices = fidxs,
                .is_mut = col.is_mut,
            });
        },
        .aosoa => |w| {
            const tname = try std.fmt.allocPrint(alloc, "{s}Tile{d}", .{ rec.name, w });
            const vname = try std.fmt.allocPrint(alloc, "{s}AoSoA{s}", .{ rec.name, if (col.is_mut) "Mut" else "" });
            for (aosoa_out.items) |prev| {
                if (std.mem.eql(u8, prev.view_name, vname)) return;
            }
            try aosoa_out.append(alloc, .{
                .tile_name = tname,
                .view_name = vname,
                .ridx = col.ridx,
                .width = w,
                .is_mut = col.is_mut,
            });
        },
        .aos => {},
    }
}

fn emitRustCallbackFnPtrTy(
    checked: *const sema.CheckedModule,
    ft: sema.FnTy,
    writer: *Io.Writer,
) Io.Writer.Error!void {
    try writer.writeAll("unsafe extern \"C\" fn(");
    var first = true;
    for (ft.params) |cp| {
        if (!first) try writer.writeAll(", ");
        first = false;
        if (cp.* == .string) {
            try writer.writeAll("*const u8, usize");
        } else if (isSliceTy(cp)) {
            const sl = unwrapSliceTy(cp);
            try writer.writeAll(if (sl.mutable) "*mut " else "*const ");
            try emitRustABITy(checked, sl.elem, writer);
            try writer.writeAll(", usize");
        } else {
            try emitRustABITy(checked, cp, writer);
        }
    }
    try writer.writeByte(')');
    if (ft.ret.* != .unit and ft.ret.* != .err) {
        try writer.writeAll(" -> ");
        try emitRustABITy(checked, ft.ret, writer);
    }
}

fn emitRustClosureParamAndRet(
    checked: *const sema.CheckedModule,
    ft: sema.FnTy,
    writer: *Io.Writer,
) Io.Writer.Error!void {
    try writer.writeByte('(');
    for (ft.params, 0..) |cp, ci| {
        if (ci > 0) try writer.writeAll(", ");
        if (cp.* == .string) {
            try writer.writeAll("&str");
        } else if (isSliceTy(cp)) {
            const sl = unwrapSliceTy(cp);
            try writer.writeAll(if (sl.mutable) "&mut [" else "&[");
            try emitRustABITy(checked, sl.elem, writer);
            try writer.writeByte(']');
        } else if (cp.* == .view and (cp.view.target.* == .record or cp.view.target.* == .applied)) {
            try writer.writeAll(if (cp.view.mode == .shared) "&" else "&mut ");
            try emitRustABITy(checked, cp.view.target, writer);
        } else {
            try emitRustABITy(checked, cp, writer);
        }
    }
    try writer.writeByte(')');
    if (ft.ret.* != .unit and ft.ret.* != .err) {
        try writer.writeAll(" -> ");
        try emitRustABITy(checked, ft.ret, writer);
    }
}

fn emitExternCShimEntry(
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    checked: *const sema.CheckedModule,
    ent: RustFFIEntry,
    is_cargo_crate: bool,
    use_cross_lto: bool,
    writer: *Io.Writer,
) Io.Writer.Error!void {
    try writer.print("#[allow(improper_ctypes_definitions)]\n#[no_mangle]\npub unsafe extern \"C\" fn {s}(\n", .{ent.sym_name});
    const pcount = if (ent.ast_extern) |ef| ef.params.len else ent.param_types.len;
    var has_soa_param = false;
    for (0..pcount) |pi| {
        const pty: ?*const sema.Ty = if (pi < ent.param_types.len) ent.param_types[pi] else null;
        if (pty != null) {
            if (collectionBackingRecord(checked, pty.?)) |col| {
                if (col.layout.layout == .soa) has_soa_param = true;
            }
        }
    }
    for (0..pcount) |pi| {
        const pname = if (pi < ent.param_names.len) ent.param_names[pi] else "arg";
        const pty: ?*const sema.Ty = if (pi < ent.param_types.len) ent.param_types[pi] else null;
        if (pty != null and pty.?.* == .string) {
            try writer.print("    {s}_ptr: *const u8,\n    {s}_len: usize,\n", .{ pname, pname });
        } else if (pty != null and pty.?.* == .fn_ty) {
            try writer.print("    {s}_cb: ", .{pname});
            try emitRustCallbackFnPtrTy(checked, pty.?.fn_ty, writer);
            try writer.writeAll(",\n");
        } else if (pty != null and isSliceTy(pty.?)) {
            const sl = unwrapSliceTy(pty.?);
            const qual = if (sl.mutable) "*mut " else "*const ";
            try writer.print("    {s}_ptr: {s}", .{ pname, qual });
            try emitRustABITy(checked, sl.elem, writer);
            try writer.print(",\n    {s}_len: usize,\n", .{pname});
        } else if (ent.ast_extern != null and pi < ent.ast_extern.?.params.len and ent.ast_extern.?.params[pi].ty != null and ent.ast_extern.?.params[pi].ty.?.* == .slice) {
            const sl = ent.ast_extern.?.params[pi].ty.?.slice;
            const qual = if (sl.mutable) "*mut " else "*const ";
            try writer.print("    {s}_ptr: {s}", .{ pname, qual });
            try emitRustAstTy(source, sl.elem, writer);
            try writer.print(",\n    {s}_len: usize,\n", .{pname});
        } else if (pty != null and collectionBackingRecord(checked, pty.?) != null) {
            const col = collectionBackingRecord(checked, pty.?).?;
            const rec = checked.records[col.ridx];
            switch (col.layout.layout) {
                .soa => {
                    const fidxs = collectFieldIndices(alloc, source, rec, pty.?);
                    const qual = if (col.is_mut) "*mut " else "*const ";
                    for (fidxs) |fi| {
                        const f = rec.fields[fi];
                        try writer.print("    {s}_{s}_ptr: {s}", .{ pname, f.name, qual });
                        try emitRustABITy(checked, f.ty, writer);
                        try writer.writeAll(",\n");
                    }
                    try writer.print("    {s}_len: usize,\n", .{pname});
                },
                .aosoa => |w| {
                    const qual = if (col.is_mut) "*mut " else "*const ";
                    try writer.print("    {s}_tiles: {s}{s}Tile{d},\n    {s}_base: usize,\n    {s}_len: usize,\n", .{ pname, qual, rec.name, w, pname, pname });
                },
                .aos => {},
            }
        } else {
            try writer.print("    {s}: ", .{pname});
            if (pty) |t| {
                try emitRustABITy(checked, t, writer);
            } else if (ent.ast_extern != null and pi < ent.ast_extern.?.params.len and ent.ast_extern.?.params[pi].ty != null) {
                try emitRustAstTy(source, ent.ast_extern.?.params[pi].ty.?, writer);
            } else {
                try writer.writeAll("usize");
            }
            try writer.writeAll(",\n");
        }
    }
    try writer.writeByte(')');
    if (ent.ret_type.* != .unit and ent.ret_type.* != .err) {
        try writer.writeAll(" -> ");
        try emitRustABITy(checked, ent.ret_type, writer);
    } else if (ent.ast_extern != null and ent.ast_extern.?.ret != null) {
        try writer.writeAll(" -> ");
        try emitRustAstTy(source, ent.ast_extern.?.ret.?, writer);
    }
    try writer.writeAll(" {\n");

    for (0..pcount) |pi| {
        const pname = if (pi < ent.param_names.len) ent.param_names[pi] else "arg";
        const pty: ?*const sema.Ty = if (pi < ent.param_types.len) ent.param_types[pi] else null;
        if (pty != null and pty.?.* == .string) {
            try writer.print("    let {s}: &str = if {s}_len == 0 {{ \"\" }} else {{ core::str::from_utf8(core::slice::from_raw_parts({s}_ptr, {s}_len)).expect(\"aethel: invalid UTF-8 string across FFI\") }};\n", .{ pname, pname, pname, pname });
        } else if (pty != null and pty.?.* == .fn_ty) {
            const ft = pty.?.fn_ty;
            try writer.print("    let {s} = move |", .{pname});
            for (ft.params, 0..) |cp, ci| {
                if (ci > 0) try writer.writeAll(", ");
                if (cp.* == .string) {
                    try writer.print("__c_{d}: &str", .{ci});
                } else if (isSliceTy(cp)) {
                    const sl = unwrapSliceTy(cp);
                    try writer.print("__c_{d}: {s}", .{ ci, if (sl.mutable) "&mut [" else "&[" });
                    try emitRustABITy(checked, sl.elem, writer);
                    try writer.writeByte(']');
                } else if (cp.* == .view and (cp.view.target.* == .record or cp.view.target.* == .applied)) {
                    try writer.print("__c_{d}: {s}", .{ ci, if (cp.view.mode == .shared) "&" else "&mut " });
                    try emitRustABITy(checked, cp.view.target, writer);
                } else {
                    try writer.print("__c_{d}: ", .{ci});
                    try emitRustABITy(checked, cp, writer);
                }
            }
            try writer.print("| {{ unsafe {{ {s}_cb(", .{pname});
            for (ft.params, 0..) |cp, ci| {
                if (ci > 0) try writer.writeAll(", ");
                if (cp.* == .string) {
                    try writer.print("if __c_{d}.is_empty() {{ core::ptr::NonNull::<u8>::dangling().as_ptr() }} else {{ __c_{d}.as_ptr() }}, __c_{d}.len()", .{ ci, ci, ci });
                } else if (isSliceTy(cp)) {
                    const sl = unwrapSliceTy(cp);
                    if (sl.mutable) {
                        try writer.print("if __c_{d}.is_empty() {{ core::ptr::NonNull::dangling().as_ptr() }} else {{ __c_{d}.as_mut_ptr() }}, __c_{d}.len()", .{ ci, ci, ci });
                    } else {
                        try writer.print("if __c_{d}.is_empty() {{ core::ptr::NonNull::dangling().as_ptr() }} else {{ __c_{d}.as_ptr() }}, __c_{d}.len()", .{ ci, ci, ci });
                    }
                } else if (cp.* == .view and (cp.view.target.* == .record or cp.view.target.* == .applied)) {
                    try writer.print("__c_{d} as {s}_", .{ ci, if (cp.view.mode == .shared) "*const " else "*mut " });
                } else {
                    try writer.print("__c_{d}", .{ci});
                }
            }
            try writer.writeAll(") } };\n");
        } else if (pty != null and isSliceTy(pty.?)) {
            const sl = unwrapSliceTy(pty.?);
            const slice_ref = if (sl.mutable) "&mut [" else "&[";
            const empty_expr = if (sl.mutable) "&mut []" else "&[]";
            const raw_fn = if (sl.mutable) "from_raw_parts_mut" else "from_raw_parts";
            try writer.print("    let {s}: {s}", .{ pname, slice_ref });
            try emitRustABITy(checked, sl.elem, writer);
            try writer.print("] = if {s}_len == 0 {{ {s} }} else {{ core::slice::{s}({s}_ptr, {s}_len) }};\n", .{
                pname,
                empty_expr,
                raw_fn,
                pname,
                pname,
            });
        } else if (ent.ast_extern != null and pi < ent.ast_extern.?.params.len and ent.ast_extern.?.params[pi].ty != null and ent.ast_extern.?.params[pi].ty.?.* == .slice) {
            const sl = ent.ast_extern.?.params[pi].ty.?.slice;
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
        } else if (pty != null and collectionBackingRecord(checked, pty.?) != null) {
            const col = collectionBackingRecord(checked, pty.?).?;
            const rec = checked.records[col.ridx];
            switch (col.layout.layout) {
                .soa => {
                    const fidxs = collectFieldIndices(alloc, source, rec, pty.?);
                    const empty_expr = if (col.is_mut) "&mut []" else "&[]";
                    const raw_fn = if (col.is_mut) "from_raw_parts_mut" else "from_raw_parts";
                    const slice_pre = if (col.is_mut) "&mut [" else "&[";
                    for (fidxs) |fi| {
                        const f = rec.fields[fi];
                        try writer.print("    let __soa_{d}_{s}: {s}", .{ pi, f.name, slice_pre });
                        try emitRustABITy(checked, f.ty, writer);
                        try writer.print("] = if {s}_len == 0 {{ {s} }} else {{ core::slice::{s}({s}_{s}_ptr, {s}_len) }};\n", .{
                            pname,
                            empty_expr,
                            raw_fn,
                            pname,
                            f.name,
                            pname,
                        });
                    }
                },
                .aosoa => |w| {
                    const vname = std.fmt.allocPrint(alloc, "{s}AoSoA{s}", .{ rec.name, if (col.is_mut) "Mut" else "" }) catch rec.name;
                    const empty_expr = if (col.is_mut) "&mut []" else "&[]";
                    const raw_fn = if (col.is_mut) "from_raw_parts_mut" else "from_raw_parts";
                    try writer.print("    let {s}_ntiles = if {s}_len == 0 {{ 0 }} else {{ ({s}_base + {s}_len + {d}) / {d} }};\n", .{
                        pname,
                        pname,
                        pname,
                        pname,
                        w - 1,
                        w,
                    });
                    try writer.print("    let {s} = {s} {{\n        tiles: if {s}_len == 0 {{ {s} }} else {{ core::slice::{s}({s}_tiles, {s}_ntiles) }},\n        base_elem: {s}_base,\n        len: {s}_len,\n    }};\n", .{
                        pname,
                        vname,
                        pname,
                        empty_expr,
                        raw_fn,
                        pname,
                        pname,
                        pname,
                        pname,
                    });
                },
                .aos => {},
            }
        }
    }

    const wrap_ret = is_cargo_crate and (ent.ret_type.* == .record or ent.ret_type.* == .applied);
    if (has_soa_param) {
        // Call the Rust callee inside a helper whose `&'a mut [T]` / `&'a [T]` slice parameters
        // preserve LLVM `noalias` / `!noalias` metadata across optimization. Under Cross-LTO
        // `#[inline(always)]` exposes `noalias` across the LTO module; otherwise `#[inline(never)]`
        // keeps the `noalias` parameter boundary intact without overlap checks.
        try writer.print("    {s}\n    fn __aethel_soa_noalias_call<'a", .{
            if (use_cross_lto) "#[inline(always)]" else "#[inline(never)]",
        });
        for (0..pcount) |pi| {
            const pty: ?*const sema.Ty = if (pi < ent.param_types.len) ent.param_types[pi] else null;
            if (pty != null and pty.?.* == .fn_ty) {
                try writer.print(", F{d}: Fn", .{pi});
                try emitRustClosureParamAndRet(checked, pty.?.fn_ty, writer);
            }
        }
        try writer.writeAll(">(\n");
        for (0..pcount) |pi| {
            const pname = if (pi < ent.param_names.len) ent.param_names[pi] else "arg";
            const pty: ?*const sema.Ty = if (pi < ent.param_types.len) ent.param_types[pi] else null;
            if (pty != null and collectionBackingRecord(checked, pty.?) != null) {
                const col = collectionBackingRecord(checked, pty.?).?;
                const rec = checked.records[col.ridx];
                if (col.layout.layout == .soa) {
                    const fidxs = collectFieldIndices(alloc, source, rec, pty.?);
                    const ref_ty = if (col.is_mut) "&'a mut [" else "&'a [";
                    for (fidxs) |fi| {
                        const f = rec.fields[fi];
                        try writer.print("        __soa_{d}_{s}: {s}", .{ pi, f.name, ref_ty });
                        try emitRustABITy(checked, f.ty, writer);
                        try writer.writeAll("],\n");
                    }
                    try writer.print("        __soa_{d}_len: usize,\n", .{pi});
                } else {
                    const w = col.layout.layout.aosoa;
                    _ = w;
                    const vname = std.fmt.allocPrint(alloc, "{s}AoSoA{s}", .{ rec.name, if (col.is_mut) "Mut" else "" }) catch rec.name;
                    try writer.print("        {s}: {s}<'a>,\n", .{ pname, vname });
                }
            } else if (pty != null and pty.?.* == .string) {
                try writer.print("        {s}: &'a str,\n", .{pname});
            } else if (pty != null and pty.?.* == .fn_ty) {
                try writer.print("        {s}: F{d},\n", .{ pname, pi });
            } else if (pty != null and isSliceTy(pty.?)) {
                const sl = unwrapSliceTy(pty.?);
                const slice_ref = if (sl.mutable) "&'a mut [" else "&'a [";
                try writer.print("        {s}: {s}", .{ pname, slice_ref });
                try emitRustABITy(checked, sl.elem, writer);
                try writer.writeAll("],\n");
            } else if (pty) |t| {
                try writer.print("        {s}: ", .{pname});
                try emitRustABITy(checked, t, writer);
                try writer.writeAll(",\n");
            }
        }
        try writer.writeByte(')');
        if (ent.ret_type.* != .unit and ent.ret_type.* != .err) {
            try writer.writeAll(" -> ");
            try emitRustABITy(checked, ent.ret_type, writer);
        } else if (ent.ast_extern != null and ent.ast_extern.?.ret != null) {
            try writer.writeAll(" -> ");
            try emitRustAstTy(source, ent.ast_extern.?.ret.?, writer);
        }
        try writer.writeAll(" {\n");
        for (0..pcount) |pi| {
            const pname = if (pi < ent.param_names.len) ent.param_names[pi] else "arg";
            const pty: ?*const sema.Ty = if (pi < ent.param_types.len) ent.param_types[pi] else null;
            if (pty != null and collectionBackingRecord(checked, pty.?) != null) {
                const col = collectionBackingRecord(checked, pty.?).?;
                const rec = checked.records[col.ridx];
                if (col.layout.layout == .soa) {
                    const fidxs = collectFieldIndices(alloc, source, rec, pty.?);
                    const qname = makeSoaQueryName(alloc, rec, fidxs, col.is_mut);
                    try writer.print("        let {s} = {s} {{\n", .{ pname, qname });
                    for (fidxs) |fi| {
                        const f = rec.fields[fi];
                        try writer.print("            {s}: __soa_{d}_{s},\n", .{ f.name, pi, f.name });
                    }
                    try writer.print("            len: __soa_{d}_len,\n        }};\n", .{pi});
                }
            }
        }
        try writer.writeAll("    ");
    }

    if (wrap_ret) {
        if (ent.is_external_crate_call) {
            try writer.print("    core::mem::transmute({s}(", .{ent.call_path});
        } else {
            try writer.print("    core::mem::transmute(aethel_rust_user::{s}(", .{ent.call_path});
        }
    } else if (ent.is_external_crate_call) {
        try writer.print("    {s}(", .{ent.call_path});
    } else {
        try writer.print("    aethel_rust_user::{s}(", .{ent.call_path});
    }
    for (0..pcount) |pi| {
        if (pi > 0) try writer.writeAll(", ");
        const pname = if (pi < ent.param_names.len) ent.param_names[pi] else "arg";
        const pty: ?*const sema.Ty = if (pi < ent.param_types.len) ent.param_types[pi] else null;
        if (is_cargo_crate and pty != null and (pty.?.* == .record or pty.?.* == .applied)) {
            try writer.print("core::mem::transmute({s})", .{pname});
        } else {
            try writer.writeAll(pname);
        }
    }
    if (wrap_ret) {
        try writer.writeAll(")");
    }
    try writer.writeAll(")\n");

    if (has_soa_param) {
        try writer.writeAll("    }\n    __aethel_soa_noalias_call(");
        var need_comma = false;
        for (0..pcount) |pi| {
            const pname = if (pi < ent.param_names.len) ent.param_names[pi] else "arg";
            const pty: ?*const sema.Ty = if (pi < ent.param_types.len) ent.param_types[pi] else null;
            if (pty != null and collectionBackingRecord(checked, pty.?) != null) {
                const col = collectionBackingRecord(checked, pty.?).?;
                const rec = checked.records[col.ridx];
                if (col.layout.layout == .soa) {
                    const fidxs = collectFieldIndices(alloc, source, rec, pty.?);
                    for (fidxs) |fi| {
                        const f = rec.fields[fi];
                        if (need_comma) try writer.writeAll(", ");
                        try writer.print("__soa_{d}_{s}", .{ pi, f.name });
                        need_comma = true;
                    }
                    if (need_comma) try writer.writeAll(", ");
                    try writer.print("{s}_len", .{pname});
                    need_comma = true;
                    continue;
                }
            }
            if (need_comma) try writer.writeAll(", ");
            try writer.writeAll(pname);
            need_comma = true;
        }
        try writer.writeAll(")\n");
    }
    try writer.writeAll("}\n");
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

fn emitRustABITy(checked: *const sema.CheckedModule, ty: *const sema.Ty, writer: *Io.Writer) Io.Writer.Error!void {
    switch (ty.*) {
        .opaque_ty => try writer.writeAll("*mut core::ffi::c_void"),
        .record => |ri| {
            if (ri < checked.records.len) {
                try writer.writeAll(checked.records[ri].name);
            } else {
                try writer.writeAll("*mut core::ffi::c_void");
            }
        },
        .applied => |ap| {
            if (ap.kind == .record and ap.decl_idx < checked.records.len) {
                try writer.writeAll(checked.records[ap.decl_idx].name);
            } else {
                try writer.writeAll("*mut core::ffi::c_void");
            }
        },
        .view => |v| {
            if (v.target.* == .opaque_ty) {
                if (v.mode == .shared) {
                    try writer.writeAll("*const core::ffi::c_void");
                } else {
                    try writer.writeAll("*mut core::ffi::c_void");
                }
            } else if (v.target.* == .record or v.target.* == .applied) {
                try writer.writeAll(if (v.mode == .shared) "*const " else "*mut ");
                try emitRustABITy(checked, v.target, writer);
            } else {
                try emitRustScalarTy(ty, writer);
            }
        },
        .path_borrow => |pb| {
            if (pb.base.* == .record or pb.base.* == .applied) {
                try writer.writeAll(if (pb.mode != null and pb.mode.? == .shared) "*const " else "*mut ");
                try emitRustABITy(checked, pb.base, writer);
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

fn hasRustStructDef(src: []const u8, name: []const u8) bool {
    var needle_buf: [128]u8 = undefined;
    const needle = std.fmt.bufPrint(&needle_buf, "struct {s}", .{name}) catch return false;
    return std.mem.indexOf(u8, src, needle) != null;
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

fn parseCargoPackageName(arena: std.mem.Allocator, toml: []const u8) ?[]const u8 {
    var in_pkg = false;
    var it = std.mem.splitScalar(u8, toml, '\n');
    while (it.next()) |line| {
        const trimmed = std.mem.trim(u8, line, " \t\r");
        if (trimmed.len == 0 or trimmed[0] == '#') continue;
        if (trimmed[0] == '[') {
            in_pkg = std.mem.eql(u8, trimmed, "[package]");
            continue;
        }
        if (in_pkg and std.mem.startsWith(u8, trimmed, "name")) {
            if (std.mem.indexOfScalar(u8, trimmed, '=')) |eq_idx| {
                const rhs = std.mem.trim(u8, trimmed[eq_idx + 1 ..], " \t\r");
                if (rhs.len >= 2 and rhs[0] == '"' and rhs[rhs.len - 1] == '"') {
                    const raw_name = rhs[1 .. rhs.len - 1];
                    const ident = arena.dupe(u8, raw_name) catch return null;
                    for (ident) |*c| {
                        if (c.* == '-') c.* = '_';
                    }
                    return ident;
                }
            }
        }
    }
    return null;
}

/// Generate the adapter Rust file inside `.aethel-build/` and compile a `.rs` file or
/// Cargo crate (`Cargo.toml` / crate directory) with `cargo`/`rustc` into a C-ABI `.a` staticlib.
pub fn compileRustStaticlib(
    io: Io,
    arena: std.mem.Allocator,
    tree: *const ast.Ast,
    checked: *const sema.CheckedModule,
    rust_path: []const u8,
    stem: []const u8,
    stderr: *Io.Writer,
) !?[]const u8 {
    // Check if `rust_path` points to a Cargo.toml or a crate directory containing Cargo.toml.
    var manifest_opt: ?[]const u8 = null;
    var crate_dir_opt: ?[]const u8 = null;
    if (std.mem.eql(u8, std.fs.path.basename(rust_path), "Cargo.toml")) {
        manifest_opt = rust_path;
        crate_dir_opt = std.fs.path.dirname(rust_path) orelse ".";
    } else if (!std.mem.endsWith(u8, rust_path, ".rs")) {
        const cand = try std.fmt.allocPrint(arena, "{s}/Cargo.toml", .{rust_path});
        if (Io.Dir.cwd().readFileAllocOptions(io, cand, arena, .limited(1024 * 1024), .of(u8), 0)) |_| {
            manifest_opt = cand;
            crate_dir_opt = rust_path;
        } else |_| {}
    }

    Io.Dir.cwd().createDirPath(io, ".aethel-build") catch {};
    const bridge_path = try std.fmt.allocPrint(arena, ".aethel-build/{s}_rust_bridge.rs", .{stem});
    const lib_path = try std.fmt.allocPrint(arena, ".aethel-build/lib{s}_rust.a", .{stem});

    if (manifest_opt) |manifest_path| {
        const crate_dir = crate_dir_opt.?;
        const toml_src = Io.Dir.cwd().readFileAllocOptions(io, manifest_path, arena, .limited(2 * 1024 * 1024), .of(u8), 0) catch |err| {
            try stderr.print("error: failed to read Cargo manifest '{s}': {s}\n", .{ manifest_path, @errorName(err) });
            try stderr.flush();
            return null;
        };
        const crate_ident = parseCargoPackageName(arena, toml_src) orelse {
            try stderr.print("error: missing [package] name in '{s}'\n", .{manifest_path});
            try stderr.flush();
            return null;
        };

        const cargo_bins = [_][]const u8{ "cargo", "/sbin/cargo" };
        var cargo_res_opt: ?std.process.RunResult = null;
        for (cargo_bins) |cb| {
            if (std.process.run(arena, io, .{
                .argv = &.{ cb, "build", "--release", "--offline", "--manifest-path", manifest_path },
            })) |res| {
                cargo_res_opt = res;
                break;
            } else |err| {
                if (err == error.FileNotFound) continue;
                try stderr.print("error: failed to invoke '{s}': {s}\n", .{ cb, @errorName(err) });
                try stderr.flush();
                return null;
            }
        }
        const cargo_res = cargo_res_opt orelse {
            try stderr.print("error: 'cargo' not found in PATH or /sbin/cargo\n", .{});
            try stderr.flush();
            return null;
        };
        if (!cargo_res.term.success()) {
            try stderr.print("error: cargo offline build failed for '{s}':\n{s}\n", .{ manifest_path, cargo_res.stderr });
            try stderr.flush();
            return null;
        }

        const lib_rs_path = try std.fmt.allocPrint(arena, "{s}/src/lib.rs", .{crate_dir});
        const lib_rs_src: ?[]const u8 = Io.Dir.cwd().readFileAllocOptions(io, lib_rs_path, arena, .limited(8 * 1024 * 1024), .of(u8), 0) catch null;

        var bridge_buf: Io.Writer.Allocating = .init(arena);
        try emitRustAdapterInner(tree, checked, lib_rs_src, crate_ident, null, false, &bridge_buf.writer);
        Io.Dir.cwd().writeFile(io, .{ .sub_path = bridge_path, .data = bridge_buf.written() }) catch |err| {
            try stderr.print("error: failed to write Rust adapter '{s}': {s}\n", .{ bridge_path, @errorName(err) });
            try stderr.flush();
            return null;
        };

        const ext_arg = try std.fmt.allocPrint(arena, "{s}={s}/target/release/lib{s}.rlib", .{ crate_ident, crate_dir, crate_ident });
        const dep_arg = try std.fmt.allocPrint(arena, "dependency={s}/target/release/deps", .{crate_dir});

        const rustc_candidates = [_][]const u8{ "rustc", "/sbin/rustc" };
        var rc_res_opt: ?std.process.RunResult = null;
        for (rustc_candidates) |rc_bin| {
            if (std.process.run(arena, io, .{
                .argv = &.{ rc_bin, "--edition", "2021", "--crate-type", "staticlib", "-C", "panic=abort", "-O", "--extern", ext_arg, "-L", dep_arg, "-o", lib_path, bridge_path },
            })) |res| {
                rc_res_opt = res;
                break;
            } else |err| {
                if (err == error.FileNotFound) continue;
                return null;
            }
        }
        const rc_res = rc_res_opt orelse return null;
        if (!rc_res.term.success()) {
            try stderr.print("error: rustc failed to link Cargo bridge '{s}':\n{s}\n", .{ bridge_path, rc_res.stderr });
            try stderr.flush();
            return null;
        }
        return lib_path;
    }

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
                "-C",
                "target-cpu=native",
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

pub const CargoBuildResult = struct {
    staticlib_path: []const u8,
    link_flags: []const []const u8,
};

fn writeCargoTomlQuoted(writer: anytype, s: []const u8) !void {
    try writer.writeByte('"');
    for (s) |c| {
        switch (c) {
            '\\' => try writer.writeAll("\\\\"),
            '"' => try writer.writeAll("\\\""),
            '\n' => try writer.writeAll("\\n"),
            else => try writer.writeByte(c),
        }
    }
    try writer.writeByte('"');
}

pub fn parseNativeStaticLibs(alloc: std.mem.Allocator, stderr_text: []const u8) ![]const []const u8 {
    var flags: std.ArrayList([]const u8) = .empty;
    var seen_lc = false;
    var lines = std.mem.splitScalar(u8, stderr_text, '\n');
    while (lines.next()) |line| {
        const needle = "native-static-libs:";
        const idx = std.mem.indexOf(u8, line, needle) orelse continue;
        const rest = std.mem.trim(u8, line[idx + needle.len ..], " \t\r");
        var toks = std.mem.tokenizeAny(u8, rest, " \t\r");
        while (toks.next()) |tok| {
            if (!std.mem.startsWith(u8, tok, "-l")) continue;
            if (std.mem.eql(u8, tok, "-lBstatic") or std.mem.eql(u8, tok, "-lBdynamic")) continue;
            if (std.mem.eql(u8, tok, "-lc")) seen_lc = true;
            var dup = false;
            for (flags.items) |prev| {
                if (std.mem.eql(u8, prev, tok)) {
                    dup = true;
                    break;
                }
            }
            if (!dup) try flags.append(alloc, try alloc.dupe(u8, tok));
        }
    }
    if (!seen_lc) try flags.append(alloc, "-lc");
    var has_gcc_s = false;
    for (flags.items) |f| {
        if (std.mem.eql(u8, f, "-lgcc_s")) {
            has_gcc_s = true;
            break;
        }
    }
    if (!has_gcc_s) try flags.append(alloc, "-lgcc_s");
    return try flags.toOwnedSlice(alloc);
}

/// Generate a managed Cargo `staticlib` crate inside `<project_root>/.aethel-build/cargo_<pkg>/`
/// combining `aethel.toml` `[rust-dependencies]`, optional `rust/src/lib.rs`, and generated
/// C-ABI shims, compile it with `cargo rustc -- --print=native-static-libs`, and return the
/// `.a` archive path plus discovered native system link flags.
pub const CargoBuildOptions = struct {
    use_cross_lto: bool = false,
    quiet_on_fail: bool = false,
};

pub fn compileCargoProjectStaticlib(
    io: Io,
    arena: std.mem.Allocator,
    tree: *const ast.Ast,
    checked: *const sema.CheckedModule,
    project_root: []const u8,
    proj_manifest: *const manifest.ProjectManifest,
    user_bridge_path: ?[]const u8,
    release_mode: bool,
    offline: bool,
    stderr: *Io.Writer,
) !?CargoBuildResult {
    return compileCargoProjectStaticlibOpts(
        io,
        arena,
        tree,
        checked,
        project_root,
        proj_manifest,
        user_bridge_path,
        release_mode,
        offline,
        .{},
        stderr,
    );
}

pub fn compileCargoProjectStaticlibOpts(
    io: Io,
    arena: std.mem.Allocator,
    tree: *const ast.Ast,
    checked: *const sema.CheckedModule,
    project_root: []const u8,
    proj_manifest: *const manifest.ProjectManifest,
    user_bridge_path: ?[]const u8,
    release_mode: bool,
    offline: bool,
    opts: CargoBuildOptions,
    stderr: *Io.Writer,
) !?CargoBuildResult {
    const norm_pkg = try manifest.normalizeCrateIdentAlloc(arena, proj_manifest.pkg_name);
    const cargo_dir = try manifest.resolveFromDir(arena, project_root, try std.fmt.allocPrint(arena, ".aethel-build/cargo_{s}", .{norm_pkg}));
    const cargo_src_dir = try std.fmt.allocPrint(arena, "{s}/src", .{cargo_dir});
    Io.Dir.cwd().createDirPath(io, cargo_src_dir) catch |err| {
        try stderr.print("error: failed to create Cargo adapter directory '{s}': {s}\n", .{ cargo_src_dir, @errorName(err) });
        try stderr.flush();
        return null;
    };

    const cargo_toml_path = try std.fmt.allocPrint(arena, "{s}/Cargo.toml", .{cargo_dir});
    const cargo_lib_rs_path = try std.fmt.allocPrint(arena, "{s}/src/lib.rs", .{cargo_dir});
    const cargo_config_path = try std.fmt.allocPrint(arena, "{s}/cargo_build.toml", .{cargo_dir});

    var toml_buf: Io.Writer.Allocating = .init(arena);
    const tw = &toml_buf.writer;
    try tw.writeAll("[package]\nname = \"aethel_cargo_bridge\"\nversion = \"0.1.0\"\nedition = ");
    try writeCargoTomlQuoted(tw, proj_manifest.rust_edition);
    try tw.writeAll("\n\n[workspace]\n\n[lib]\nname = \"aethel_cargo_bridge\"\npath = \"src/lib.rs\"\ncrate-type = [\"staticlib\"]\n\n");
    try tw.writeAll("[profile.dev]\npanic = \"abort\"\n\n[profile.release]\nopt-level = 3\ncodegen-units = 1\npanic = \"abort\"\n\n[dependencies]\n");

    for (proj_manifest.rust_deps) |rd| {
        var resolved_dep = rd;
        if (rd.path) |rp| {
            const joined = try manifest.resolveFromDir(arena, project_root, rp);
            const abs = Io.Dir.cwd().realPathFileAlloc(io, joined, arena) catch joined;
            resolved_dep.path = abs;
        }
        try manifest.renderRustDepLine(tw, resolved_dep);
    }

    Io.Dir.cwd().writeFile(io, .{ .sub_path = cargo_toml_path, .data = toml_buf.written() }) catch |err| {
        try stderr.print("error: failed to write '{s}': {s}\n", .{ cargo_toml_path, @errorName(err) });
        try stderr.flush();
        return null;
    };

    if (release_mode) {
        const cfg_data: []const u8 = if (opts.use_cross_lto)
            "[build]\nrustflags = [\"-C\", \"target-cpu=native\", \"-C\", \"linker-plugin-lto\"]\n"
        else
            "[build]\nrustflags = [\"-C\", \"target-cpu=native\"]\n";
        Io.Dir.cwd().writeFile(io, .{ .sub_path = cargo_config_path, .data = cfg_data }) catch |err| {
            try stderr.print("error: failed to write '{s}': {s}\n", .{ cargo_config_path, @errorName(err) });
            try stderr.flush();
            return null;
        };
    }

    var user_rust_src: ?[]const u8 = null;
    if (user_bridge_path) |bp| {
        user_rust_src = Io.Dir.cwd().readFileAllocOptions(io, bp, arena, .limited(16 * 1024 * 1024), .of(u8), 0) catch |err| {
            try stderr.print("error: failed to read Rust bridge '{s}': {s}\n", .{ bp, @errorName(err) });
            try stderr.flush();
            return null;
        };
    }

    var adapter_buf: Io.Writer.Allocating = .init(arena);
    try emitCargoProjectAdapterWithOptions(tree, checked, user_rust_src, proj_manifest.pkg_name, opts.use_cross_lto, &adapter_buf.writer);
    Io.Dir.cwd().writeFile(io, .{ .sub_path = cargo_lib_rs_path, .data = adapter_buf.written() }) catch |err| {
        try stderr.print("error: failed to write '{s}': {s}\n", .{ cargo_lib_rs_path, @errorName(err) });
        try stderr.flush();
        return null;
    };

    const proj_lock = try manifest.resolveFromDir(arena, project_root, "Cargo.lock");
    const gen_lock = try std.fmt.allocPrint(arena, "{s}/Cargo.lock", .{cargo_dir});
    if (Io.Dir.cwd().readFileAllocOptions(io, proj_lock, arena, .limited(16 * 1024 * 1024), .of(u8), 0)) |lock_data| {
        Io.Dir.cwd().writeFile(io, .{ .sub_path = gen_lock, .data = lock_data }) catch {};
    } else |_| {}

    const cargo_bins = [_][]const u8{ "cargo", "/sbin/cargo" };
    var cargo_res_opt: ?std.process.RunResult = null;
    for (cargo_bins) |cb| {
        var argv: std.ArrayList([]const u8) = .empty;
        try argv.appendSlice(arena, &.{ cb, "rustc" });
        if (release_mode) {
            try argv.append(arena, "--release");
            try argv.appendSlice(arena, &.{ "--config", cargo_config_path });
        }
        if (offline) try argv.append(arena, "--offline");
        try argv.appendSlice(arena, &.{ "--manifest-path", cargo_toml_path, "--lib", "--", "--print=native-static-libs" });

        if (std.process.run(arena, io, .{ .argv = argv.items })) |res| {
            cargo_res_opt = res;
            break;
        } else |err| {
            if (err == error.FileNotFound) continue;
            try stderr.print("error: failed to invoke '{s}': {s}\n", .{ cb, @errorName(err) });
            try stderr.flush();
            return null;
        }
    }

    const cargo_res = cargo_res_opt orelse {
        try stderr.print("error: 'cargo' not found in PATH or /sbin/cargo\n", .{});
        try stderr.flush();
        return null;
    };
    if (!cargo_res.term.success()) {
        if (!opts.quiet_on_fail) {
            try stderr.print("error: cargo build failed for '{s}':\n{s}\n", .{ proj_manifest.pkg_name, cargo_res.stderr });
            try stderr.flush();
        }
        return null;
    }

    if (Io.Dir.cwd().readFileAllocOptions(io, gen_lock, arena, .limited(16 * 1024 * 1024), .of(u8), 0)) |new_lock| {
        Io.Dir.cwd().writeFile(io, .{ .sub_path = proj_lock, .data = new_lock }) catch {};
    } else |_| {}

    const profile_dir = if (release_mode) "release" else "debug";
    const staticlib_path = try std.fmt.allocPrint(arena, "{s}/target/{s}/libaethel_cargo_bridge.a", .{ cargo_dir, profile_dir });
    const link_flags = try parseNativeStaticLibs(arena, cargo_res.stderr);

    return .{
        .staticlib_path = staticlib_path,
        .link_flags = link_flags,
    };
}
