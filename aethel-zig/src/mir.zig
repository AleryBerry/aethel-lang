const std = @import("std");
const Io = std.Io;
const sema = @import("sema.zig");

pub const current_mir_version: u32 = 1;

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

    for (checked.functions) |fun| {
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

        try writer.writeAll("end_fn\n");
    }
}

fn allFieldsScalarRepresentable(fields: []const sema.CheckedField) bool {
    for (fields) |f| {
        if (f.ty.* == .record or f.ty.* == .tuple or f.ty.* == .err) return false;
        if (f.bits == 0) return false;
    }
    return true;
}
