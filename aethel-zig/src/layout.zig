const std = @import("std");

pub const StoragePolicy = enum {
    addressable,
    may_share_byte,
};

pub const ConflictPair = struct {
    a: usize,
    b: usize,
};

pub const Slot = struct {
    size: usize,
    alignment: usize,
};

pub const FieldSchema = struct {
    name: []const u8,
    bits: u16,
    signed: bool,
    addressable_size: usize,
    addressable_align: usize,
    is_subbyte_packable: bool,
};

pub const FieldPlacement = struct {
    byte_offset: usize,
    bit_offset: ?u8,
    size: usize,
    alignment: usize,
    bits: u16,
    policy: StoragePolicy,
};

pub const RecordLayout = struct {
    size: usize,
    alignment: usize,
    fields: []const FieldPlacement,
};

pub const CollectionLayout = union(enum) {
    aos,
    soa,
    aosoa: usize,

    pub fn isValid(self: CollectionLayout) bool {
        return switch (self) {
            .aos, .soa => true,
            .aosoa => |w| w > 0,
        };
    }
};

pub const CompactADTLayout = struct {
    tag_bits: u16,
    max_payload_bits: u16,
    total_bits: u16,
    total_bytes: usize,
    can_share_byte: bool,
};

/// Natural ABI alignment matching `Aethel.naturalAlignment`:
/// caps at 16 bytes for wide multi-word integers.
pub fn naturalAlignment(payload_bytes: usize) usize {
    if (payload_bytes <= 1) return 1;
    if (payload_bytes <= 2) return 2;
    if (payload_bytes <= 4) return 4;
    if (payload_bytes <= 8) return 8;
    return 16;
}

pub fn alignUp(offset: usize, alignment: usize) usize {
    if (alignment <= 1) return offset;
    const rem = offset % alignment;
    if (rem == 0) return offset;
    return offset + (alignment - rem);
}

/// Target integer ABI slot matching `TargetIntegerABI.natural` in `IntegerLayout.lean`.
pub fn naturalSlot(bits: u16) Slot {
    const payload_bytes: usize = (@as(usize, bits) + 7) / 8;
    const alignment = naturalAlignment(payload_bytes);
    return .{
        .size = alignUp(payload_bytes, alignment),
        .alignment = alignment,
    };
}

pub fn planCompactADT(variant_count: usize, max_payload_bits: u16) CompactADTLayout {
    const tag_bits: u16 = if (variant_count <= 1)
        0
    else if (variant_count == 2)
        1
    else if (variant_count <= 4)
        2
    else if (variant_count <= 8)
        3
    else if (variant_count <= 16)
        4
    else blk: {
        var b: u16 = 5;
        var cap: usize = 32;
        while (cap < variant_count and b < 16) : (b += 1) {
            cap *= 2;
        }
        break :blk b;
    };
    const total_bits = tag_bits + max_payload_bits;
    const total_bytes: usize = (@as(usize, total_bits) + 7) / 8;
    return .{
        .tag_bits = tag_bits,
        .max_payload_bits = max_payload_bits,
        .total_bits = total_bits,
        .total_bytes = @max(@as(usize, 1), total_bytes),
        .can_share_byte = total_bits < 8,
    };
}

/// Synthesize co-borrow-safe field layout matching `Aethel.CoBorrowPacking.autoPlan`
/// and `Aethel.AutomaticLayout.plan` (stable alignment ordering + FFD sub-byte bins).
pub fn planRecordLayout(
    alloc: std.mem.Allocator,
    fields: []const FieldSchema,
    conflicts: []const ConflictPair,
) std.mem.Allocator.Error!RecordLayout {
    if (fields.len == 0) {
        return .{ .size = 0, .alignment = 1, .fields = &.{} };
    }

    const policies = try alloc.alloc(StoragePolicy, fields.len);
    for (fields, 0..) |_, i| {
        var conflict = false;
        for (conflicts) |edge| {
            if (edge.a < fields.len and edge.b < fields.len and edge.a != edge.b) {
                if (edge.a == i or edge.b == i) {
                    conflict = true;
                    break;
                }
            }
        }
        policies[i] = if (conflict) .addressable else .may_share_byte;
    }

    const decl = try computeCandidate(alloc, fields, policies, false);
    const compact = try computeCandidate(alloc, fields, policies, true);
    if (compact.size < decl.size) {
        return compact;
    }
    return decl;
}

const Indexed = struct {
    idx: usize,
    schema: FieldSchema,
    policy: StoragePolicy,
};

fn computeCandidate(
    alloc: std.mem.Allocator,
    fields: []const FieldSchema,
    policies: []const StoragePolicy,
    compact: bool,
) std.mem.Allocator.Error!RecordLayout {
    var max_align: usize = 1;
    var ordinary: std.ArrayList(Indexed) = .empty;
    var packed_list: std.ArrayList(Indexed) = .empty;

    for (fields, 0..) |f, idx| {
        const a = @max(@as(usize, 1), f.addressable_align);
        if (a > max_align) max_align = a;
        const entry = Indexed{ .idx = idx, .schema = f, .policy = policies[idx] };
        const packable = compact and f.is_subbyte_packable and policies[idx] == .may_share_byte and f.bits > 0 and f.bits < 8;
        if (packable) {
            try packed_list.append(alloc, entry);
        } else {
            try ordinary.append(alloc, entry);
        }
    }

    if (compact) {
        // Stable descending sort by addressable alignment (`≥` preserves earlier index on ties).
        stableSortByAlignDesc(ordinary.items);
        // Stable descending sort by bit width.
        stableSortByBitsDesc(packed_list.items);
    }

    const out = try alloc.alloc(FieldPlacement, fields.len);
    var cursor: usize = 0;

    for (ordinary.items) |entry| {
        const a = @max(@as(usize, 1), entry.schema.addressable_align);
        const offset = alignUp(cursor, a);
        cursor = offset + entry.schema.addressable_size;
        out[entry.idx] = .{
            .byte_offset = offset,
            .bit_offset = null,
            .size = entry.schema.addressable_size,
            .alignment = a,
            .bits = entry.schema.bits,
            .policy = entry.policy,
        };
    }

    // First-fit-decreasing sub-byte bin packing (matches `AutomaticLayout.allocPackedBit`).
    var bins: std.ArrayList(u16) = .empty;
    for (packed_list.items) |entry| {
        var placed = false;
        for (bins.items, 0..) |*used, bin_idx| {
            if (used.* + entry.schema.bits <= 8) {
                const bit_off: u8 = @intCast(used.*);
                used.* += entry.schema.bits;
                out[entry.idx] = .{
                    .byte_offset = cursor + bin_idx,
                    .bit_offset = bit_off,
                    .size = 1,
                    .alignment = 1,
                    .bits = entry.schema.bits,
                    .policy = entry.policy,
                };
                placed = true;
                break;
            }
        }
        if (!placed) {
            const bin_idx = bins.items.len;
            try bins.append(alloc, entry.schema.bits);
            out[entry.idx] = .{
                .byte_offset = cursor + bin_idx,
                .bit_offset = 0,
                .size = 1,
                .alignment = 1,
                .bits = entry.schema.bits,
                .policy = entry.policy,
            };
        }
    }

    const total_size = alignUp(cursor + bins.items.len, max_align);
    return .{
        .size = total_size,
        .alignment = max_align,
        .fields = out,
    };
}

fn stableSortByAlignDesc(items: []Indexed) void {
    var i: usize = 1;
    while (i < items.len) : (i += 1) {
        const key = items[i];
        var j = i;
        while (j > 0 and items[j - 1].schema.addressable_align < key.schema.addressable_align) : (j -= 1) {
            items[j] = items[j - 1];
        }
        items[j] = key;
    }
}

fn stableSortByBitsDesc(items: []Indexed) void {
    var i: usize = 1;
    while (i < items.len) : (i += 1) {
        const key = items[i];
        var j = i;
        while (j > 0 and items[j - 1].schema.bits < key.schema.bits) : (j -= 1) {
            items[j] = items[j - 1];
        }
        items[j] = key;
    }
}
