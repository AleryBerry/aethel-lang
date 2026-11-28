const std = @import("std");
const Io = std.Io;
const sema = @import("sema.zig");
const law_verifier = @import("law_verifier.zig");

pub const current_mir_version: u32 = 1;

const RootBase = struct {
    root_name: []const u8,
    base_offset: usize,
};

const ViewSlot = struct {
    view_id: usize,
    offset: usize,
};

const VarEntry = struct {
    base: []const u8,
    version: u32,
};

/// Emit a versioned `.mir` v1 certificate module consumable by Lean's
/// `lake exe aethel-check <file.mir>` (`Aethel/MIRValidator.lean`).
pub fn emitMir(checked: *const sema.CheckedModule, writer: *Io.Writer) Io.Writer.Error!void {
    try writer.print("mir_version {d}\n", .{current_mir_version});

    for (checked.records) |rec| {
        if (!allFieldsScalarRepresentable(rec.fields)) continue;
        try writer.print("record {s} {d}\n", .{ rec.name, rec.record_layout.size });
        for (rec.fields) |f| {
            const prefix: u8 = if (f.signed) 'i' else 'u';
            const bits: u16 = @max(@as(u16, 1), f.bits);
            try writer.print("  field {c}{d}\n", .{ prefix, bits });
        }
        if (rec.is_flat_c) {
            try writer.writeAll("  flat\n");
        } else {
            for (rec.record_layout.fields, 0..) |fp, fi| {
                const bits: u16 = @max(@as(u16, 1), rec.fields[fi].bits);
                if (fp.policy == .addressable and (bits % 8 != 0)) {
                    var has_conflict = false;
                    for (rec.conflicts) |c| {
                        if (c.a == fi or c.b == fi) {
                            has_conflict = true;
                            break;
                        }
                    }
                    if (!has_conflict) {
                        try writer.print("  addressable {d}\n", .{fi});
                    }
                }
            }
        }
        for (rec.conflicts) |c| {
            try writer.print("  conflict {d} {d}\n", .{ c.a, c.b });
        }
        try writer.writeAll("end_record\n");
    }

    for (checked.collections) |col| {
        try writer.print("collection {s} ", .{col.name});
        switch (col.layout) {
            .aos => try writer.writeAll("aos"),
            .soa => try writer.writeAll("soa"),
            .aosoa => |w| try writer.print("aosoa {d}", .{w}),
        }
        try writer.print(" {d}\n", .{col.field_count});
    }

    for (checked.dyn_vecs) |dv| {
        try writer.print("dyn_vec {s} ", .{dv.name});
        switch (dv.layout) {
            .aos => try writer.writeAll("aos"),
            .soa => try writer.writeAll("soa"),
            .aosoa => |w| try writer.print("aosoa {d}", .{w}),
        }
        try writer.print(" {d} 8\n", .{dv.field_count});
    }

    for (checked.functions) |fun| {
        if (fun.has_extern_abi) continue;
        try writer.print("fn {s}\n", .{fun.name});
        for (fun.writes) |w| {
            try writer.print("  effect_write {d}\n", .{w.field_idx});
        }
        for (fun.preserves) |pidx| {
            try writer.print("  preserves {d}\n", .{pidx});
        }

        if (fun.reads.len > 0 or fun.writes.len > 0) {
            const rec_size: usize = if (fun.target_record) |ridx|
                @max(@as(usize, 1), checked.records[ridx].record_layout.size)
            else
                16;
            try writer.print("  alloc 0 {d}\n", .{rec_size});
            var step_id: usize = 0;

            for (fun.reads) |r| {
                var off: usize = 0;
                if (r.record_idx < checked.records.len and r.field_idx < checked.records[r.record_idx].record_layout.fields.len) {
                    const byte_off = checked.records[r.record_idx].record_layout.fields[r.field_idx].byte_offset;
                    if (byte_off < rec_size) off = byte_off;
                }
                try writer.print("  alias {d} 0 {d} shared\n", .{ step_id, off });
                try writer.print("  reserve {d} {d} shared\n", .{ step_id, step_id });
                try writer.print("  read_view {d}\n", .{step_id});
                try writer.print("  release {d}\n", .{step_id});
                try writer.print("  forget {d}\n", .{step_id});
                step_id += 1;
            }

            for (fun.writes) |w| {
                var off: usize = 0;
                if (w.record_idx < checked.records.len and w.field_idx < checked.records[w.record_idx].record_layout.fields.len) {
                    const byte_off = checked.records[w.record_idx].record_layout.fields[w.field_idx].byte_offset;
                    if (byte_off < rec_size) off = byte_off;
                }
                try writer.print("  alias {d} 0 {d} exclusive\n", .{ step_id, off });
                try writer.print("  reserve {d} {d} exclusive\n", .{ step_id, step_id });
                try writer.print("  write_view {d} 1\n", .{step_id});
                try writer.print("  release {d}\n", .{step_id});
                try writer.print("  forget {d}\n", .{step_id});
                step_id += 1;
            }

            try writer.writeAll("  destroy 0\n");
        }

        try emitPermTrace(checked, fun.perm_trace, writer);
        try emitDisjointCerts(fun.disjoint_certs, writer);
        try emitDecreasesCerts(fun.decreases_certs, writer);

        try writer.writeAll("end_fn\n");
    }

    for (checked.laws) |law| {
        for (law.symbolic_certs) |sc| {
            const kw = if (sc.is_trait_law and sc.kind == .always)
                "trait_law"
            else switch (sc.kind) {
                .always => "law_always",
                .never => "law_never",
            };
            try writer.print("{s} {s}\n", .{ kw, sc.name });
            for (sc.hyps) |hp| {
                try writer.writeAll("  hyp ");
                try law_verifier.emitLawPropMir(writer, hp);
                try writer.writeByte('\n');
            }
            try writer.writeAll("  goal ");
            try law_verifier.emitLawPropMir(writer, sc.goal);
            try writer.writeByte('\n');
            try writer.writeAll("end_law\n");
        }
    }
}

fn emitDecreasesCerts(certs: []const law_verifier.DecreasesCertEmit, writer: *Io.Writer) Io.Writer.Error!void {
    for (certs) |dc| {
        try writer.print("  decreases {d}", .{dc.guards.len});
        for (dc.guards) |gp| {
            try writer.writeByte(' ');
            try law_verifier.emitLawPropMir(writer, gp);
        }
        try writer.writeByte(' ');
        try law_verifier.emitLawExprMir(writer, dc.cur_measure);
        try writer.writeByte(' ');
        try law_verifier.emitLawExprMir(writer, dc.next_measure);
        try writer.writeByte('\n');
    }
}

fn emitPermTrace(
    checked: *const sema.CheckedModule,
    trace: []const sema.PermTraceOp,
    writer: *Io.Writer,
) Io.Writer.Error!void {
    if (trace.len == 0) return;

    var roots_buf: [64]RootBase = undefined;
    var roots_len: usize = 0;
    var total_alloc: usize = 0;

    var slots_buf: [256]ViewSlot = undefined;
    var slots_len: usize = 0;

    for (trace) |op| {
        if (op == .reserve) {
            const rv = op.reserve;
            var root_base: ?usize = null;
            for (roots_buf[0..roots_len]) |rb| {
                if (std.mem.eql(u8, rb.root_name, rv.root_name)) {
                    root_base = rb.base_offset;
                    break;
                }
            }
            if (root_base == null and roots_len < roots_buf.len) {
                const sz: usize = if (rv.record_idx < checked.records.len)
                    @max(@as(usize, 1), checked.records[rv.record_idx].record_layout.size)
                else
                    16;
                root_base = total_alloc;
                roots_buf[roots_len] = .{ .root_name = rv.root_name, .base_offset = total_alloc };
                roots_len += 1;
                total_alloc += sz;
            }
            const base = root_base orelse 0;
            var field_off: usize = 0;
            if (rv.field_idx) |fi| {
                if (rv.record_idx < checked.records.len and fi < checked.records[rv.record_idx].record_layout.fields.len) {
                    field_off = checked.records[rv.record_idx].record_layout.fields[fi].byte_offset;
                }
            }
            if (slots_len < slots_buf.len) {
                slots_buf[slots_len] = .{ .view_id = rv.view_id, .offset = base + field_off };
                slots_len += 1;
            }
        }
    }

    if (total_alloc == 0) return;
    try writer.print("  perm_alloc {d}\n", .{total_alloc});

    for (trace) |op| {
        switch (op) {
            .reserve => |rv| {
                var off: usize = 0;
                for (slots_buf[0..slots_len]) |sl| {
                    if (sl.view_id == rv.view_id) {
                        off = sl.offset;
                        break;
                    }
                }
                try writer.print("  perm_reserve {d} {d} {s}\n", .{ rv.view_id, off, rv.perm.mirName() });
            },
            .activate => |a| try writer.print("  perm_activate {d}\n", .{a.view_id}),
            .freeze => |fz| try writer.print("  perm_freeze {d}\n", .{fz.view_id}),
            .read => |rd| try writer.print("  perm_read {d}\n", .{rd.view_id}),
            .write => |wr| try writer.print("  perm_write {d} {d}\n", .{ wr.view_id, wr.val }),
            .release => |rl| try writer.print("  perm_release {d}\n", .{rl.view_id}),
        }
    }
}

fn findOrAddVar(vars: *[64]VarEntry, vars_len: *usize, af: sema.AffineForm) void {
    const b = af.base orelse return;
    for (vars[0..vars_len.*]) |v| {
        if (std.mem.eql(u8, v.base, b) and v.version == af.base_version) return;
    }
    if (vars_len.* < vars.len) {
        vars[vars_len.*] = .{ .base = b, .version = af.base_version };
        vars_len.* += 1;
    }
}

fn lookupVarId(vars: []const VarEntry, af: sema.AffineForm) ?usize {
    const b = af.base orelse return null;
    for (vars, 0..) |v, idx| {
        if (std.mem.eql(u8, v.base, b) and v.version == af.base_version) return idx;
    }
    return null;
}

fn emitIdxExpr(writer: *Io.Writer, vars: []const VarEntry, af: sema.AffineForm) Io.Writer.Error!void {
    if (lookupVarId(vars, af)) |id| {
        if (af.offset == 0) {
            try writer.print("v{d}", .{id});
        } else {
            try writer.print("v{d}+{d}", .{ id, af.offset });
        }
    } else {
        try writer.print("{d}", .{af.offset});
    }
}

fn emitDisjointCerts(certs: []const sema.DisjointCertEmit, writer: *Io.Writer) Io.Writer.Error!void {
    for (certs) |cert| {
        var vars_buf: [64]VarEntry = undefined;
        var vars_len: usize = 0;

        switch (cert.kind) {
            .idx_ne => |p| {
                if (!p.a.isPureNat() or !p.b.isPureNat()) continue;
                findOrAddVar(&vars_buf, &vars_len, p.a);
                findOrAddVar(&vars_buf, &vars_len, p.b);
            },
            .slice_disjoint => |s| {
                if (!s.s1.lo.isPureNat() or !s.s1.hi.isPureNat() or
                    !s.s2.lo.isPureNat() or !s.s2.hi.isPureNat()) continue;
                findOrAddVar(&vars_buf, &vars_len, s.s1.lo);
                findOrAddVar(&vars_buf, &vars_len, s.s1.hi);
                findOrAddVar(&vars_buf, &vars_len, s.s2.lo);
                findOrAddVar(&vars_buf, &vars_len, s.s2.hi);
            },
        }
        const vars = vars_buf[0..vars_len];

        for (cert.facts) |f| {
            if (!f.lhs.isPureNat() or !f.rhs.isPureNat()) continue;
            if ((f.kind == .lt or f.kind == .le) and (f.lhs.base == null or f.rhs.base == null or f.lhs.offset != 0 or f.rhs.offset != 0)) {
                continue;
            }
            findOrAddVar(&vars_buf, &vars_len, f.lhs);
            findOrAddVar(&vars_buf, &vars_len, f.rhs);
        }
        const all_vars = vars_buf[0..vars_len];
        _ = vars;

        switch (cert.kind) {
            .idx_ne => |p| {
                try writer.writeAll("  disjoint_idx ");
                try emitFactEnvTok(writer, all_vars, cert.facts);
                try writer.writeByte(' ');
                try emitIdxExpr(writer, all_vars, p.a);
                try writer.writeByte(' ');
                try emitIdxExpr(writer, all_vars, p.b);
                try writer.writeByte('\n');
            },
            .slice_disjoint => |s| {
                try writer.writeAll("  disjoint_slice ");
                try emitFactEnvTok(writer, all_vars, cert.facts);
                try writer.writeByte(' ');
                try emitIdxExpr(writer, all_vars, s.s1.lo);
                try writer.writeByte(' ');
                try emitIdxExpr(writer, all_vars, s.s1.hi);
                try writer.writeByte(' ');
                try emitIdxExpr(writer, all_vars, s.s2.lo);
                try writer.writeByte(' ');
                try emitIdxExpr(writer, all_vars, s.s2.hi);
                try writer.writeByte('\n');
            },
        }
    }
}

fn emitFactEnvTok(writer: *Io.Writer, vars: []const VarEntry, facts: []const sema.OrderFact) Io.Writer.Error!void {
    var wrote_any = false;
    for (facts) |f| {
        if (!f.lhs.isPureNat() or !f.rhs.isPureNat()) continue;
        switch (f.kind) {
            .ne => {
                if (wrote_any) try writer.writeByte(';');
                wrote_any = true;
                try writer.writeAll("ne:");
                try emitIdxExpr(writer, vars, f.lhs);
                try writer.writeByte(',');
                try emitIdxExpr(writer, vars, f.rhs);
            },
            .lt, .le => {
                if (f.lhs.base == null or f.rhs.base == null or f.lhs.offset != 0 or f.rhs.offset != 0) continue;
                const lid = lookupVarId(vars, f.lhs) orelse continue;
                const rid = lookupVarId(vars, f.rhs) orelse continue;
                if (wrote_any) try writer.writeByte(';');
                wrote_any = true;
                try writer.print("{s}:v{d},v{d}", .{ if (f.kind == .lt) "lt" else "le", lid, rid });
            },
        }
    }
    if (!wrote_any) {
        try writer.writeAll("none");
    }
}

fn allFieldsScalarRepresentable(fields: []const sema.CheckedField) bool {
    for (fields) |f| {
        if (f.ty.* == .record or f.ty.* == .tuple or f.ty.* == .err) return false;
        if (f.bits == 0) return false;
    }
    return true;
}
