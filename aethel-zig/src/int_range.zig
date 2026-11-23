const std = @import("std");
const lexer = @import("lexer.zig");

/// Arbitrary bit-width scalar integer descriptor (`bits` in `1..=65535`).
pub const IntType = struct {
    signed: bool,
    bits: u16,

    pub fn format(self: IntType, writer: *std.Io.Writer) std.Io.Writer.Error!void {
        try writer.print("{c}{d}", .{ if (self.signed) @as(u8, 'i') else @as(u8, 'u'), self.bits });
    }
};

/// Exact number of binary bits needed to represent `n` (`bitLength(0) == 0`).
pub fn bitLength(n: u128) u16 {
    if (n == 0) return 0;
    return @as(u16, 128) - @as(u16, @intCast(@clz(n)));
}

/// Minimum unsigned bit width (`>= 1`) required to represent `n`.
pub fn minUnsignedBits(n: u128) u16 {
    return @max(@as(u16, 1), bitLength(n));
}

/// Minimum signed bit width (`>= 1`) required for two's complement `[lo, hi]`.
pub fn minSignedBits(lo: i128, hi: i128) u16 {
    const lo_mag: u128 = if (lo < 0) blk: {
        // -lo - 1 safely computed without overflowing `minInt(i128)`:
        // if lo == -1, mag = 0; if lo == minInt(i128), -lo - 1 = 2^127 - 1.
        const neg_minus_one: i128 = -(lo + 1);
        break :blk @intCast(neg_minus_one);
    } else 0;
    const hi_mag: u128 = if (hi >= 0) @intCast(hi) else 0;
    return bitLength(@max(lo_mag, hi_mag)) + 1;
}

/// Closed integer interval `[lo, hi]` with exact i128 arithmetic up to 126-bit types
/// and safe width-based representation for huge `127..=65535`-bit types.
pub const IntRange = union(enum) {
    bounded: struct {
        lo: i128,
        hi: i128,
    },
    wide: IntType,

    pub fn singleton(c: i128) IntRange {
        return .{ .bounded = .{ .lo = c, .hi = c } };
    }

    pub fn ofType(ty: IntType) IntRange {
        if (!ty.signed) {
            if (ty.bits <= 126) {
                const max_val: i128 = (@as(i128, 1) << @intCast(ty.bits)) - 1;
                return .{ .bounded = .{ .lo = 0, .hi = max_val } };
            }
            return .{ .wide = ty };
        } else {
            if (ty.bits <= 127) {
                const shift: u7 = @intCast(ty.bits - 1);
                const half: i128 = @as(i128, 1) << shift;
                return .{ .bounded = .{ .lo = -half, .hi = half - 1 } };
            }
            return .{ .wide = ty };
        }
    }

    pub fn fitsType(self: IntRange, ty: IntType) bool {
        switch (self) {
            .bounded => |b| return fitsI128(b.lo, ty) and fitsI128(b.hi, ty),
            .wide => |w| {
                if (!ty.signed) {
                    return !w.signed and w.bits <= ty.bits;
                }
                if (w.signed) {
                    return w.bits <= ty.bits;
                }
                return w.bits < ty.bits;
            },
        }
    }

    pub fn containsRange(outer: IntRange, inner: IntRange) bool {
        switch (outer) {
            .bounded => |ob| switch (inner) {
                .bounded => |ib| return ib.lo >= ob.lo and ib.hi <= ob.hi,
                .wide => return false,
            },
            .wide => |wt| return inner.fitsType(wt),
        }
    }

    pub fn add(a: IntRange, b: IntRange) ?IntRange {
        switch (a) {
            .bounded => |ba| switch (b) {
                .bounded => |bb| {
                    const lo_res = @addWithOverflow(ba.lo, bb.lo);
                    const hi_res = @addWithOverflow(ba.hi, bb.hi);
                    if (lo_res[1] != 0 or hi_res[1] != 0) return null;
                    return .{ .bounded = .{ .lo = lo_res[0], .hi = hi_res[0] } };
                },
                .wide => |wb| return widenSum(.{ .signed = ba.lo < 0, .bits = inferBitsI128(ba.lo, ba.hi) orelse 128 }, wb),
            },
            .wide => |wa| switch (b) {
                .bounded => |bb| return widenSum(wa, .{ .signed = bb.lo < 0, .bits = inferBitsI128(bb.lo, bb.hi) orelse 128 }),
                .wide => |wb| return widenSum(wa, wb),
            },
        }
    }

    pub fn sub(a: IntRange, b: IntRange) ?IntRange {
        const neg_b = b.neg() orelse return null;
        return a.add(neg_b);
    }

    pub fn neg(a: IntRange) ?IntRange {
        switch (a) {
            .bounded => |b| {
                const neg_hi = @subWithOverflow(@as(i128, 0), b.hi);
                const neg_lo = @subWithOverflow(@as(i128, 0), b.lo);
                if (neg_hi[1] != 0 or neg_lo[1] != 0) return null;
                return .{ .bounded = .{ .lo = neg_hi[0], .hi = neg_lo[0] } };
            },
            .wide => |w| {
                if (w.bits >= lexer.max_int_bits) return null;
                return .{ .wide = .{ .signed = true, .bits = w.bits + 1 } };
            },
        }
    }

    pub fn mul(a: IntRange, b: IntRange) ?IntRange {
        switch (a) {
            .bounded => |ba| switch (b) {
                .bounded => |bb| {
                    const c1 = @mulWithOverflow(ba.lo, bb.lo);
                    const c2 = @mulWithOverflow(ba.lo, bb.hi);
                    const c3 = @mulWithOverflow(ba.hi, bb.lo);
                    const c4 = @mulWithOverflow(ba.hi, bb.hi);
                    if (c1[1] != 0 or c2[1] != 0 or c3[1] != 0 or c4[1] != 0) return null;
                    return .{ .bounded = .{
                        .lo = @min(@min(c1[0], c2[0]), @min(c3[0], c4[0])),
                        .hi = @max(@max(c1[0], c2[0]), @max(c3[0], c4[0])),
                    } };
                },
                .wide => |wb| return widenMul(.{ .signed = ba.lo < 0, .bits = inferBitsI128(ba.lo, ba.hi) orelse 128 }, wb),
            },
            .wide => |wa| switch (b) {
                .bounded => |bb| return widenMul(wa, .{ .signed = bb.lo < 0, .bits = inferBitsI128(bb.lo, bb.hi) orelse 128 }),
                .wide => |wb| return widenMul(wa, wb),
            },
        }
    }

    pub fn join(a: IntRange, b: IntRange) IntRange {
        switch (a) {
            .bounded => |ba| switch (b) {
                .bounded => |bb| return .{ .bounded = .{
                    .lo = @min(ba.lo, bb.lo),
                    .hi = @max(ba.hi, bb.hi),
                } },
                .wide => |wb| {
                    const ta = inferIntegerType(a) orelse return .{ .wide = wb };
                    return .{ .wide = commonWide(ta, wb) };
                },
            },
            .wide => |wa| switch (b) {
                .bounded => {
                    const tb = inferIntegerType(b) orelse return .{ .wide = wa };
                    return .{ .wide = commonWide(wa, tb) };
                },
                .wide => |wb| return .{ .wide = commonWide(wa, wb) },
            },
        }
    }

    pub fn narrowUpper(self: IntRange, bound: i128) ?IntRange {
        switch (self) {
            .bounded => |b| {
                const hi = @min(b.hi, bound);
                if (b.lo > hi) return null;
                return .{ .bounded = .{ .lo = b.lo, .hi = hi } };
            },
            .wide => |w| {
                if (!w.signed) {
                    if (bound < 0) return null;
                    return .{ .bounded = .{ .lo = 0, .hi = bound } };
                }
                return null;
            },
        }
    }

    pub fn narrowLower(self: IntRange, bound: i128) ?IntRange {
        switch (self) {
            .bounded => |b| {
                const lo = @max(b.lo, bound);
                if (lo > b.hi) return null;
                return .{ .bounded = .{ .lo = lo, .hi = b.hi } };
            },
            .wide => return null,
        }
    }
};

fn commonWide(a: IntType, b: IntType) IntType {
    if (a.signed or b.signed) {
        const a_need: u16 = if (a.signed) a.bits else @min(lexer.max_int_bits, a.bits +| 1);
        const b_need: u16 = if (b.signed) b.bits else @min(lexer.max_int_bits, b.bits +| 1);
        return .{ .signed = true, .bits = @max(a_need, b_need) };
    }
    return .{ .signed = false, .bits = @max(a.bits, b.bits) };
}

fn widenSum(a: IntType, b: IntType) ?IntRange {
    const base = commonWide(a, b);
    if (base.bits >= lexer.max_int_bits) return null;
    return .{ .wide = .{ .signed = base.signed, .bits = base.bits + 1 } };
}

fn widenMul(a: IntType, b: IntType) ?IntRange {
    const sum: u32 = @as(u32, a.bits) + @as(u32, b.bits);
    if (sum > lexer.max_int_bits) return null;
    return .{ .wide = .{ .signed = a.signed or b.signed, .bits = @intCast(sum) } };
}

fn inferBitsI128(lo: i128, hi: i128) ?u16 {
    const bits = if (lo >= 0) minUnsignedBits(@intCast(hi)) else minSignedBits(lo, hi);
    return bits;
}

pub fn fitsI128(val: i128, ty: IntType) bool {
    if (!ty.signed) {
        if (val < 0) return false;
        if (ty.bits >= 127) return true;
        const limit: i128 = @as(i128, 1) << @intCast(ty.bits);
        return val < limit;
    } else {
        if (ty.bits >= 128) return true;
        const shift: u7 = @intCast(ty.bits - 1);
        const half: i128 = @as(i128, 1) << shift;
        return val >= -half and val < half;
    }
}

/// Synthesize the provably minimal `IntType` (`1..=65535` bits) covering `range`.
pub fn inferIntegerType(range: IntRange) ?IntType {
    switch (range) {
        .wide => |w| {
            if (w.bits < 1 or w.bits > lexer.max_int_bits) return null;
            return w;
        },
        .bounded => |b| {
            if (b.lo > b.hi) return null;
            if (b.lo >= 0) {
                const bits = minUnsignedBits(@intCast(b.hi));
                if (bits > lexer.max_int_bits) return null;
                return .{ .signed = false, .bits = bits };
            } else {
                const bits = minSignedBits(b.lo, b.hi);
                if (bits > lexer.max_int_bits) return null;
                return .{ .signed = true, .bits = bits };
            }
        },
    }
}

pub const ParsedIntLit = struct {
    value: u128,
    suffix: ?IntType,
};

/// Parse integer literal lexeme (`123`, `0xff_u8`, `42i7`, `1_u65535`) into magnitude + optional suffix.
pub fn parseIntLiteral(lexeme: []const u8) ?ParsedIntLit {
    if (lexeme.len == 0) return null;
    var radix: u8 = 10;
    var start: usize = 0;
    if (lexeme.len >= 2 and lexeme[0] == '0') {
        switch (lexeme[1]) {
            'x', 'X' => {
                radix = 16;
                start = 2;
            },
            'b', 'B' => {
                radix = 2;
                start = 2;
            },
            'o', 'O' => {
                radix = 8;
                start = 2;
            },
            else => {},
        }
    }

    // Locate optional `u...` or `i...` suffix at end.
    var mantissa_end = lexeme.len;
    var suffix: ?IntType = null;
    for (lexeme[start..], start..) |ch, idx| {
        if ((ch == 'u' or ch == 'i') and (radix != 16 or idx > start)) {
            if (lexer.parseIntWidth(lexeme[idx..])) |iw| {
                suffix = .{ .signed = iw.signed, .bits = iw.bits };
                mantissa_end = idx;
                break;
            }
        }
    }

    var acc: u128 = 0;
    var saw_digit = false;
    for (lexeme[start..mantissa_end]) |ch| {
        if (ch == '_') continue;
        const d: u128 = switch (ch) {
            '0'...'9' => ch - '0',
            'a'...'f' => ch - 'a' + 10,
            'A'...'F' => ch - 'A' + 10,
            else => return null,
        };
        if (d >= radix) return null;
        const mul_res = @mulWithOverflow(acc, radix);
        if (mul_res[1] != 0) return null;
        const add_res = @addWithOverflow(mul_res[0], d);
        if (add_res[1] != 0) return null;
        acc = add_res[0];
        saw_digit = true;
    }
    if (!saw_digit) return null;
    return .{ .value = acc, .suffix = suffix };
}

pub fn fitsNonNeg(val: u128, ty: IntType) bool {
    if (!ty.signed) {
        if (ty.bits >= 128) return true;
        const limit: u128 = @as(u128, 1) << @intCast(ty.bits);
        return val < limit;
    } else {
        if (ty.bits > 128) return true;
        const limit: u128 = @as(u128, 1) << @intCast(ty.bits - 1);
        return val < limit;
    }
}

pub fn fitsSignedNegated(mag: u128, ty: IntType) bool {
    if (!ty.signed) return mag == 0;
    if (ty.bits > 128) return true;
    if (ty.bits == 128) return mag <= (@as(u128, 1) << 127);
    const limit: u128 = @as(u128, 1) << @intCast(ty.bits - 1);
    return mag <= limit;
}
