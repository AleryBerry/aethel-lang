const std = @import("std");
const Io = std.Io;
const ast = @import("ast.zig");
const sema = @import("sema.zig");

const RustFFIEntry = struct {
    sym_name: []const u8,
    call_path: []const u8,
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
    return emitRustAdapterInner(tree, checked, user_rust_source, null, writer);
}

fn emitRustAdapterInner(
    tree: *const ast.Ast,
    checked: *const sema.CheckedModule,
    user_rust_source: ?[]const u8,
    cargo_crate_ident: ?[]const u8,
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
        for (checked.foreign_contracts) |fc| {
            if (std.mem.eql(u8, fc.aethel_name, cname) and fc.rust_target != null) {
                call_path = std.fmt.allocPrint(alloc, "{s}::{s}", .{ fc.rust_target.?, sym }) catch sym;
                break;
            }
        }
        const pnames = alloc.alloc([]const u8, fd.params.len) catch continue;
        for (fd.params, 0..) |p, pi| pnames[pi] = p.name.slice(tree.source);
        entries[entries_len] = .{
            .sym_name = sym,
            .call_path = call_path,
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
            try writer.writeAll("\n// Verified flat C-ABI mirror structs (RustComplexABI.lean)\n");
            emitted_header = true;
        }
        try writer.print("#[repr(C)]\n#[derive(Copy, Clone, Debug)]\npub struct {s} {{\n", .{rec.name});
        for (rec.fields) |f| {
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
        try emitExternCShimEntry(alloc, tree.source, checked, ent, cargo_crate_ident != null, writer);
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

fn emitExternCShimEntry(
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    checked: *const sema.CheckedModule,
    ent: RustFFIEntry,
    is_cargo_crate: bool,
    writer: *Io.Writer,
) Io.Writer.Error!void {
    try writer.print("#[no_mangle]\npub unsafe extern \"C\" fn {s}(\n", .{ent.sym_name});
    const pcount = if (ent.ast_extern) |ef| ef.params.len else ent.param_types.len;
    for (0..pcount) |pi| {
        const pname = if (pi < ent.param_names.len) ent.param_names[pi] else "arg";
        const pty: ?*const sema.Ty = if (pi < ent.param_types.len) ent.param_types[pi] else null;
        if (pty != null and isSliceTy(pty.?)) {
            const sl = unwrapSliceTy(pty.?);
            const qual = if (sl.mutable) "*mut " else "*const ";
            try writer.print("    {s}_ptr: {s}", .{ pname, qual });
            try emitRustScalarTy(sl.elem, writer);
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
                    const qname = makeSoaQueryName(alloc, rec, fidxs, col.is_mut);
                    const empty_expr = if (col.is_mut) "&mut []" else "&[]";
                    const raw_fn = if (col.is_mut) "from_raw_parts_mut" else "from_raw_parts";
                    try writer.print("    let {s} = {s} {{\n", .{ pname, qname });
                    for (fidxs) |fi| {
                        const f = rec.fields[fi];
                        try writer.print("        {s}: if {s}_len == 0 {{ {s} }} else {{ core::slice::{s}({s}_{s}_ptr, {s}_len) }},\n", .{
                            f.name,
                            pname,
                            empty_expr,
                            raw_fn,
                            pname,
                            f.name,
                            pname,
                        });
                    }
                    try writer.print("        len: {s}_len,\n    }};\n", .{pname});
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
    if (wrap_ret) {
        try writer.print("    core::mem::transmute(aethel_rust_user::{s}(", .{ent.call_path});
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

    if (manifest_opt) |manifest| {
        const crate_dir = crate_dir_opt.?;
        const toml_src = Io.Dir.cwd().readFileAllocOptions(io, manifest, arena, .limited(2 * 1024 * 1024), .of(u8), 0) catch |err| {
            try stderr.print("error: failed to read Cargo manifest '{s}': {s}\n", .{ manifest, @errorName(err) });
            try stderr.flush();
            return null;
        };
        const crate_ident = parseCargoPackageName(arena, toml_src) orelse {
            try stderr.print("error: missing [package] name in '{s}'\n", .{manifest});
            try stderr.flush();
            return null;
        };

        const cargo_bins = [_][]const u8{ "cargo", "/sbin/cargo" };
        var cargo_res_opt: ?std.process.RunResult = null;
        for (cargo_bins) |cb| {
            if (std.process.run(arena, io, .{
                .argv = &.{ cb, "build", "--release", "--offline", "--manifest-path", manifest },
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
            try stderr.print("error: cargo offline build failed for '{s}':\n{s}\n", .{ manifest, cargo_res.stderr });
            try stderr.flush();
            return null;
        }

        const lib_rs_path = try std.fmt.allocPrint(arena, "{s}/src/lib.rs", .{crate_dir});
        const lib_rs_src: ?[]const u8 = Io.Dir.cwd().readFileAllocOptions(io, lib_rs_path, arena, .limited(8 * 1024 * 1024), .of(u8), 0) catch null;

        var bridge_buf: Io.Writer.Allocating = .init(arena);
        try emitRustAdapterInner(tree, checked, lib_rs_src, crate_ident, &bridge_buf.writer);
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
