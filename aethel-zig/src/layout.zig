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
    is_packable: bool,
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

pub const LoopAccessProfile = struct {
    total_record_bytes: usize,
    hot_record_bytes: usize,
    hot_field_count: usize,
    total_field_count: usize,
    has_simd_loop: bool,
    observed_len: ?usize,
};

pub const l1_data_cache_bytes: usize = 32768;

/// Mirror `AutomaticLayout.shouldUnpackHotInL1`: unpack hot loop-mutated packable fields when the
/// record working set fits inside L1d (`32 KiB`), while always packing cold or streaming fields.
pub fn shouldUnpackHotInL1(is_hot: bool, observed_len: ?usize, naive_record_bytes: usize) bool {
    if (!is_hot) return false;
    const len = observed_len orelse return false;
    const ws = std.math.mul(usize, len, @max(@as(usize, 1), naive_record_bytes)) catch return false;
    return ws <= l1_data_cache_bytes;
}

pub const AutoLayoutDecision = struct {
    selected: CollectionLayout,
    hot_ratio_pct: usize,
    reason: []const u8,
};

/// Select an L1-cache-aware collection layout from whole-module loop access profiling,
/// mirroring `CacheLayout.selectCollectionLayout` in Lean.
pub fn selectAutoCollectionLayout(profile: LoopAccessProfile) AutoLayoutDecision {
    const total_bytes = @max(@as(usize, 1), profile.total_record_bytes);
    const hot_bytes = if (profile.hot_field_count > 0)
        @min(total_bytes, @max(@as(usize, 1), profile.hot_record_bytes))
    else
        total_bytes;
    const ratio_pct = (hot_bytes * 100) / total_bytes;

    if (!profile.has_simd_loop and profile.observed_len != null and profile.observed_len.? <= 2) {
        return .{
            .selected = .aos,
            .hot_ratio_pct = ratio_pct,
            .reason = "small collection (len <= 2) without SIMD loop; AoS avoids tile padding",
        };
    }

    const has_partial_hot_access = profile.hot_field_count > 0 and
        (profile.hot_field_count < profile.total_field_count or hot_bytes < total_bytes);

    if (profile.has_simd_loop or has_partial_hot_access) {
        if (hot_bytes * 8 <= 4096) {
            return .{
                .selected = .{ .aosoa = 8 },
                .hot_ratio_pct = ratio_pct,
                .reason = if (profile.has_simd_loop)
                    "SIMD map_in_place loop detected; AoSoA(8) packs 8 contiguous lanes per L1 tile"
                else
                    "partial hot-field scan; AoSoA(8) packs hot fields into 8-element L1 cache tiles",
            };
        }
        return .{
            .selected = .soa,
            .hot_ratio_pct = ratio_pct,
            .reason = "large sparse hot fields (>4 KiB per 8-tile); SoA isolates cold fields",
        };
    }

    if (profile.hot_field_count == 0 and total_bytes > 64 and
        profile.observed_len != null and profile.observed_len.? >= 16)
    {
        return .{
            .selected = .soa,
            .hot_ratio_pct = ratio_pct,
            .reason = "record exceeds 64B cache line on large collection; SoA improves streaming bandwidth",
        };
    }

    return .{
        .selected = .aos,
        .hot_ratio_pct = ratio_pct,
        .reason = "full-record spatial locality fits cleanly in AoS",
    };
}

/// Stably partition `items` so entries with `is_hot[i] == true` precede cold entries,
/// matching `CacheLayout.reorderHotFirst` in Lean.
pub fn reorderHotFieldsFirst(
    comptime T: type,
    alloc: std.mem.Allocator,
    items: []const T,
    is_hot: []const bool,
) std.mem.Allocator.Error![]T {
    const out = try alloc.alloc(T, items.len);
    var out_i: usize = 0;
    for (items, 0..) |item, i| {
        if (i < is_hot.len and is_hot[i]) {
            out[out_i] = item;
            out_i += 1;
        }
    }
    for (items, 0..) |item, i| {
        if (!(i < is_hot.len and is_hot[i])) {
            out[out_i] = item;
            out_i += 1;
        }
    }
    return out;
}

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

fn placeDeclarationOrder(
    alloc: std.mem.Allocator,
    fields: []const FieldSchema,
    policies: ?[]const StoragePolicy,
) std.mem.Allocator.Error!RecordLayout {
    if (fields.len == 0) {
        return .{ .size = 0, .alignment = 1, .fields = &.{} };
    }
    const out = try alloc.alloc(FieldPlacement, fields.len);
    var cursor: usize = 0;
    var max_align: usize = 1;
    for (fields, 0..) |f, idx| {
        const a = @max(@as(usize, 1), f.addressable_align);
        if (a > max_align) max_align = a;
        const offset = alignUp(cursor, a);
        cursor = offset + f.addressable_size;
        out[idx] = .{
            .byte_offset = offset,
            .bit_offset = null,
            .size = f.addressable_size,
            .alignment = a,
            .bits = f.bits,
            .policy = if (policies) |p| p[idx] else .addressable,
        };
    }
    return .{
        .size = alignUp(cursor, max_align),
        .alignment = max_align,
        .fields = out,
    };
}

pub fn planFlatCLayout(
    alloc: std.mem.Allocator,
    fields: []const FieldSchema,
) std.mem.Allocator.Error!RecordLayout {
    return placeDeclarationOrder(alloc, fields, null);
}

/// Synthesize co-borrow-safe field layout matching `Aethel.CoBorrowPacking.autoPlan`
/// and `Aethel.AutomaticLayout.plan` (alignment-sorted addressable slots + contiguous bit intervals).
pub fn planRecordLayout(
    alloc: std.mem.Allocator,
    fields: []const FieldSchema,
    conflicts: []const ConflictPair,
) std.mem.Allocator.Error!RecordLayout {
    if (fields.len == 0) {
        return .{ .size = 0, .alignment = 1, .fields = &.{} };
    }

    const policies = try alloc.alloc(StoragePolicy, fields.len);
    for (fields, 0..) |f, i| {
        var conflict = !f.is_packable;
        if (!conflict) {
            for (conflicts) |edge| {
                if (edge.a < fields.len and edge.b < fields.len and edge.a != edge.b) {
                    if (edge.a == i or edge.b == i) {
                        conflict = true;
                        break;
                    }
                }
            }
        }
        policies[i] = if (conflict) .addressable else .may_share_byte;
    }

    const decl = try placeDeclarationOrder(alloc, fields, policies);
    const compact = try computeCompactCandidate(alloc, fields, policies);
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

fn computeCompactCandidate(
    alloc: std.mem.Allocator,
    fields: []const FieldSchema,
    policies: []const StoragePolicy,
) std.mem.Allocator.Error!RecordLayout {
    var max_align: usize = 1;
    var ordinary: std.ArrayList(Indexed) = .empty;
    var packed_list: std.ArrayList(Indexed) = .empty;

    for (fields, 0..) |f, idx| {
        const entry = Indexed{ .idx = idx, .schema = f, .policy = policies[idx] };
        if (f.is_packable and policies[idx] == .may_share_byte) {
            try packed_list.append(alloc, entry);
        } else {
            const a = @max(@as(usize, 1), f.addressable_align);
            if (a > max_align) max_align = a;
            try ordinary.append(alloc, entry);
        }
    }

    // Stable descending sort by addressable alignment (`≥` preserves earlier index on ties).
    stableSortByAlignDesc(ordinary.items);
    // Stable descending sort by bit width.
    stableSortByBitsDesc(packed_list.items);

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

    // Contiguous bit-interval packing across byte boundaries (matches `AutomaticLayout.compactCandidate`).
    var bit_cursor: usize = cursor * 8;
    for (packed_list.items) |entry| {
        const byte_off = bit_cursor / 8;
        const bit_off: u8 = @intCast(bit_cursor % 8);
        const span_bytes: usize = if (entry.schema.bits == 0)
            0
        else
            (@as(usize, bit_off) + @as(usize, entry.schema.bits) + 7) / 8;
        out[entry.idx] = .{
            .byte_offset = byte_off,
            .bit_offset = bit_off,
            .size = span_bytes,
            .alignment = 1,
            .bits = entry.schema.bits,
            .policy = entry.policy,
        };
        bit_cursor += entry.schema.bits;
    }

    const total_size = alignUp((bit_cursor + 7) / 8, max_align);
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
