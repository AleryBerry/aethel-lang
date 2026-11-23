const std = @import("std");
const Io = std.Io;
const ast = @import("ast.zig");
const int_range = @import("int_range.zig");
const lexer = @import("lexer.zig");

/// Symbolic arithmetic expression over natural numbers matching `Aethel.LawAutoProver.LawExpr`.
pub const LawExpr = union(enum) {
    var_id: u16,
    const_val: u64,
    add: Pair,
    sub: Pair,
    mul_const: MulConst,
    min: Pair,
    max: Pair,

    pub const Pair = struct {
        a: *const LawExpr,
        b: *const LawExpr,
    };

    pub const MulConst = struct {
        c: u64,
        e: *const LawExpr,
    };

    pub fn eval(self: *const LawExpr, env: []const u64) u64 {
        return switch (self.*) {
            .var_id => |id| if (id < env.len) env[id] else 0,
            .const_val => |n| n,
            .add => |p| p.a.eval(env) +| p.b.eval(env),
            .sub => |p| p.a.eval(env) -| p.b.eval(env),
            .mul_const => |mc| mc.c *| mc.e.eval(env),
            .min => |p| @min(p.a.eval(env), p.b.eval(env)),
            .max => |p| @max(p.a.eval(env), p.b.eval(env)),
        };
    }

    pub fn eql(self: *const LawExpr, other: *const LawExpr) bool {
        if (@intFromEnum(self.*) != @intFromEnum(other.*)) return false;
        return switch (self.*) {
            .var_id => |id| id == other.var_id,
            .const_val => |n| n == other.const_val,
            .add => |p| p.a.eql(other.add.a) and p.b.eql(other.add.b),
            .sub => |p| p.a.eql(other.sub.a) and p.b.eql(other.sub.b),
            .mul_const => |mc| mc.c == other.mul_const.c and mc.e.eql(other.mul_const.e),
            .min => |p| p.a.eql(other.min.a) and p.b.eql(other.min.b),
            .max => |p| p.a.eql(other.max.a) and p.b.eql(other.max.b),
        };
    }
};

/// Symbolic proposition over natural numbers matching `Aethel.LawAutoProver.LawProp`.
pub const LawProp = union(enum) {
    tt,
    ff,
    eq: ExprPair,
    ne: ExprPair,
    le: ExprPair,
    lt: ExprPair,
    not: *const LawProp,
    and_op: PropPair,
    or_op: PropPair,
    imp: PropPair,

    pub const ExprPair = struct {
        a: *const LawExpr,
        b: *const LawExpr,
    };

    pub const PropPair = struct {
        p: *const LawProp,
        q: *const LawProp,
    };

    pub fn evalBool(self: *const LawProp, env: []const u64) bool {
        return switch (self.*) {
            .tt => true,
            .ff => false,
            .eq => |ep| ep.a.eval(env) == ep.b.eval(env),
            .ne => |ep| ep.a.eval(env) != ep.b.eval(env),
            .le => |ep| ep.a.eval(env) <= ep.b.eval(env),
            .lt => |ep| ep.a.eval(env) < ep.b.eval(env),
            .not => |inner| !inner.evalBool(env),
            .and_op => |pp| pp.p.evalBool(env) and pp.q.evalBool(env),
            .or_op => |pp| pp.p.evalBool(env) or pp.q.evalBool(env),
            .imp => |pp| !pp.p.evalBool(env) or pp.q.evalBool(env),
        };
    }
};

pub const SymbolicLawKind = enum {
    always,
    never,
};

pub const SymbolicLawCert = struct {
    name: []const u8,
    kind: SymbolicLawKind,
    hyps: []const *const LawProp,
    goal: *const LawProp,
};

pub const DecreasesCertEmit = struct {
    guards: []const *const LawProp,
    cur_measure: *const LawExpr,
    next_measure: *const LawExpr,
};

pub fn emitLawExprMir(writer: *Io.Writer, expr: *const LawExpr) Io.Writer.Error!void {
    switch (expr.*) {
        .var_id => |id| try writer.print("v{d}", .{id}),
        .const_val => |n| try writer.print("{d}", .{n}),
        .add => |p| {
            try writer.writeAll("add ");
            try emitLawExprMir(writer, p.a);
            try writer.writeByte(' ');
            try emitLawExprMir(writer, p.b);
        },
        .sub => |p| {
            try writer.writeAll("sub ");
            try emitLawExprMir(writer, p.a);
            try writer.writeByte(' ');
            try emitLawExprMir(writer, p.b);
        },
        .mul_const => |mc| {
            try writer.print("mul {d} ", .{mc.c});
            try emitLawExprMir(writer, mc.e);
        },
        .min => |p| {
            try writer.writeAll("min ");
            try emitLawExprMir(writer, p.a);
            try writer.writeByte(' ');
            try emitLawExprMir(writer, p.b);
        },
        .max => |p| {
            try writer.writeAll("max ");
            try emitLawExprMir(writer, p.a);
            try writer.writeByte(' ');
            try emitLawExprMir(writer, p.b);
        },
    }
}

pub fn emitLawPropMir(writer: *Io.Writer, prop: *const LawProp) Io.Writer.Error!void {
    switch (prop.*) {
        .tt => try writer.writeAll("tt"),
        .ff => try writer.writeAll("ff"),
        .eq => |ep| {
            try writer.writeAll("eq ");
            try emitLawExprMir(writer, ep.a);
            try writer.writeByte(' ');
            try emitLawExprMir(writer, ep.b);
        },
        .ne => |ep| {
            try writer.writeAll("ne ");
            try emitLawExprMir(writer, ep.a);
            try writer.writeByte(' ');
            try emitLawExprMir(writer, ep.b);
        },
        .le => |ep| {
            try writer.writeAll("le ");
            try emitLawExprMir(writer, ep.a);
            try writer.writeByte(' ');
            try emitLawExprMir(writer, ep.b);
        },
        .lt => |ep| {
            try writer.writeAll("lt ");
            try emitLawExprMir(writer, ep.a);
            try writer.writeByte(' ');
            try emitLawExprMir(writer, ep.b);
        },
        .not => |inner| {
            try writer.writeAll("not ");
            try emitLawPropMir(writer, inner);
        },
        .and_op => |pp| {
            try writer.writeAll("and ");
            try emitLawPropMir(writer, pp.p);
            try writer.writeByte(' ');
            try emitLawPropMir(writer, pp.q);
        },
        .or_op => |pp| {
            try writer.writeAll("or ");
            try emitLawPropMir(writer, pp.p);
            try writer.writeByte(' ');
            try emitLawPropMir(writer, pp.q);
        },
        .imp => |pp| {
            try writer.writeAll("imp ");
            try emitLawPropMir(writer, pp.p);
            try emitLawExprSpace(writer);
            try emitLawPropMir(writer, pp.q);
        },
    }
}

fn emitLawExprSpace(writer: *Io.Writer) Io.Writer.Error!void {
    try writer.writeByte(' ');
}

// =========================================================================
// Tier 2 Automated Symbolic Prover (mirroring `Aethel.LawAutoProver`)
// =========================================================================

const Term = struct {
    v: u16,
    c: u64,
};

const LinearForm = struct {
    constant: u64,
    terms: []const Term,

    fn eql(self: LinearForm, other: LinearForm) bool {
        if (self.constant != other.constant or self.terms.len != other.terms.len) return false;
        for (self.terms, other.terms) |a, b| {
            if (a.v != b.v or a.c != b.c) return false;
        }
        return true;
    }
};

fn insertTerm(alloc: std.mem.Allocator, v: u16, c: u64, xs: []const Term) std.mem.Allocator.Error![]const Term {
    if (c == 0) return xs;
    var out: std.ArrayList(Term) = .empty;
    var inserted = false;
    for (xs) |t| {
        if (!inserted and v < t.v) {
            try out.append(alloc, .{ .v = v, .c = c });
            inserted = true;
            try out.append(alloc, t);
        } else if (!inserted and v == t.v) {
            try out.append(alloc, .{ .v = v, .c = c +| t.c });
            inserted = true;
        } else {
            try out.append(alloc, t);
        }
    }
    if (!inserted) {
        try out.append(alloc, .{ .v = v, .c = c });
    }
    return try out.toOwnedSlice(alloc);
}

fn mergeTerms(alloc: std.mem.Allocator, xs: []const Term, ys: []const Term) std.mem.Allocator.Error![]const Term {
    var acc = ys;
    for (xs) |t| {
        acc = try insertTerm(alloc, t.v, t.c, acc);
    }
    return acc;
}

fn scaleTerms(alloc: std.mem.Allocator, c: u64, xs: []const Term) std.mem.Allocator.Error![]const Term {
    if (c == 0 or xs.len == 0) return &.{};
    var out = try alloc.alloc(Term, xs.len);
    for (xs, 0..) |t, i| {
        out[i] = .{ .v = t.v, .c = c *| t.c };
    }
    return out;
}

fn toLinear(alloc: std.mem.Allocator, e: *const LawExpr) ?LinearForm {
    switch (e.*) {
        .const_val => |n| return .{ .constant = n, .terms = &.{} },
        .var_id => |id| {
            const ts = alloc.alloc(Term, 1) catch return null;
            ts[0] = .{ .v = id, .c = 1 };
            return .{ .constant = 0, .terms = ts };
        },
        .add => |p| {
            const la = toLinear(alloc, p.a) orelse return null;
            const lb = toLinear(alloc, p.b) orelse return null;
            return .{
                .constant = la.constant +| lb.constant,
                .terms = mergeTerms(alloc, la.terms, lb.terms) catch return null,
            };
        },
        .mul_const => |mc| {
            if (mc.c == 0) return .{ .constant = 0, .terms = &.{} };
            const le = toLinear(alloc, mc.e) orelse return null;
            return .{
                .constant = mc.c *| le.constant,
                .terms = scaleTerms(alloc, mc.c, le.terms) catch return null,
            };
        },
        else => return null,
    }
}

fn termsSubLe(xs: []const Term, ys: []const Term) bool {
    var xi: usize = 0;
    var yi: usize = 0;
    while (xi < xs.len and yi < ys.len) {
        const tx = xs[xi];
        const ty = ys[yi];
        if (tx.v == ty.v) {
            if (tx.c > ty.c) return false;
            xi += 1;
            yi += 1;
        } else if (tx.v > ty.v) {
            yi += 1;
        } else {
            return false;
        }
    }
    return xi == xs.len;
}

fn linearLe(alloc: std.mem.Allocator, a: *const LawExpr, b: *const LawExpr) bool {
    const la = toLinear(alloc, a) orelse return false;
    const lb = toLinear(alloc, b) orelse return false;
    return la.constant <= lb.constant and termsSubLe(la.terms, lb.terms);
}

fn linearEq(alloc: std.mem.Allocator, a: *const LawExpr, b: *const LawExpr) bool {
    const la = toLinear(alloc, a) orelse return false;
    const lb = toLinear(alloc, b) orelse return false;
    return la.eql(lb);
}

fn linearLt(alloc: std.mem.Allocator, a: *const LawExpr, b: *const LawExpr) bool {
    const la = toLinear(alloc, a) orelse return false;
    const lb = toLinear(alloc, b) orelse return false;
    return la.constant < lb.constant and termsSubLe(la.terms, lb.terms);
}

fn mkLawExpr(alloc: std.mem.Allocator, val: LawExpr) *const LawExpr {
    const p = alloc.create(LawExpr) catch unreachable;
    p.* = val;
    return p;
}

fn mkLawProp(alloc: std.mem.Allocator, val: LawProp) *const LawProp {
    const p = alloc.create(LawProp) catch unreachable;
    p.* = val;
    return p;
}

pub fn normalizeLawExpr(alloc: std.mem.Allocator, e: *const LawExpr) *const LawExpr {
    return switch (e.*) {
        .var_id, .const_val => e,
        .add => |p| {
            const na = normalizeLawExpr(alloc, p.a);
            const nb = normalizeLawExpr(alloc, p.b);
            if (na.* == .const_val and na.const_val == 0) return nb;
            if (nb.* == .const_val and nb.const_val == 0) return na;
            if (na.* == .const_val and nb.* == .const_val) {
                return mkLawExpr(alloc, .{ .const_val = na.const_val +| nb.const_val });
            }
            return mkLawExpr(alloc, .{ .add = .{ .a = na, .b = nb } });
        },
        .sub => |p| {
            const na = normalizeLawExpr(alloc, p.a);
            const nb = normalizeLawExpr(alloc, p.b);
            if (na.eql(nb)) return mkLawExpr(alloc, .{ .const_val = 0 });
            if (na.* == .const_val and nb.* == .const_val) {
                return mkLawExpr(alloc, .{ .const_val = na.const_val -| nb.const_val });
            }
            if (na.* == .const_val and na.const_val == 0) return na;
            if (nb.* == .const_val and nb.const_val == 0) return na;
            return mkLawExpr(alloc, .{ .sub = .{ .a = na, .b = nb } });
        },
        .mul_const => |mc| {
            const ne = normalizeLawExpr(alloc, mc.e);
            if (mc.c == 0) return mkLawExpr(alloc, .{ .const_val = 0 });
            if (mc.c == 1) return ne;
            if (ne.* == .const_val) return mkLawExpr(alloc, .{ .const_val = mc.c *| ne.const_val });
            return mkLawExpr(alloc, .{ .mul_const = .{ .c = mc.c, .e = ne } });
        },
        .min => |p| {
            const na = normalizeLawExpr(alloc, p.a);
            const nb = normalizeLawExpr(alloc, p.b);
            if (na.eql(nb)) return na;
            if (na.* == .const_val and nb.* == .const_val) {
                return mkLawExpr(alloc, .{ .const_val = @min(na.const_val, nb.const_val) });
            }
            return mkLawExpr(alloc, .{ .min = .{ .a = na, .b = nb } });
        },
        .max => |p| {
            const na = normalizeLawExpr(alloc, p.a);
            const nb = normalizeLawExpr(alloc, p.b);
            if (na.eql(nb)) return na;
            if (na.* == .const_val and nb.* == .const_val) {
                return mkLawExpr(alloc, .{ .const_val = @max(na.const_val, nb.const_val) });
            }
            return mkLawExpr(alloc, .{ .max = .{ .a = na, .b = nb } });
        },
    };
}

fn hypImpliesLe(a: *const LawExpr, b: *const LawExpr, h: *const LawProp) bool {
    return switch (h.*) {
        .le => |ep| ep.a.eql(a) and ep.b.eql(b),
        .lt => |ep| ep.a.eql(a) and ep.b.eql(b),
        .eq => |ep| (ep.a.eql(a) and ep.b.eql(b)) or (ep.b.eql(a) and ep.a.eql(b)),
        else => false,
    };
}

fn hypImpliesEq(a: *const LawExpr, b: *const LawExpr, h: *const LawProp) bool {
    return switch (h.*) {
        .eq => |ep| (ep.a.eql(a) and ep.b.eql(b)) or (ep.b.eql(a) and ep.a.eql(b)),
        else => false,
    };
}

fn hypImpliesLt(a: *const LawExpr, b: *const LawExpr, h: *const LawProp) bool {
    return switch (h.*) {
        .lt => |ep| ep.a.eql(a) and ep.b.eql(b),
        else => false,
    };
}

fn hypImpliesNe(a: *const LawExpr, b: *const LawExpr, h: *const LawProp) bool {
    return switch (h.*) {
        .ne => |ep| (ep.a.eql(a) and ep.b.eql(b)) or (ep.b.eql(a) and ep.a.eql(b)),
        else => false,
    };
}

fn proveLe(alloc: std.mem.Allocator, hyps: []const *const LawProp, fuel: u32, a: *const LawExpr, b: *const LawExpr) bool {
    if (fuel == 0) return false;
    const f = fuel - 1;
    if (a.eql(b)) return true;
    if (a.* == .const_val and a.const_val == 0) return true;
    for (hyps) |h| if (hypImpliesLe(a, b, h)) return true;
    if (linearLe(alloc, a, b)) return true;
    if (a.* == .sub and proveLe(alloc, hyps, f, a.sub.a, b)) return true;
    if (a.* == .min and (proveLe(alloc, hyps, f, a.min.a, b) or proveLe(alloc, hyps, f, a.min.b, b))) return true;
    if (b.* == .max and (proveLe(alloc, hyps, f, a, b.max.a) or proveLe(alloc, hyps, f, a, b.max.b))) return true;
    if (a.* == .max and proveLe(alloc, hyps, f, a.max.a, b) and proveLe(alloc, hyps, f, a.max.b, b)) return true;
    if (b.* == .min and proveLe(alloc, hyps, f, a, b.min.a) and proveLe(alloc, hyps, f, a, b.min.b)) return true;
    if (a.* == .add and b.* == .add) {
        if ((proveLe(alloc, hyps, f, a.add.a, b.add.a) and proveLe(alloc, hyps, f, a.add.b, b.add.b)) or
            (proveLe(alloc, hyps, f, a.add.a, b.add.b) and proveLe(alloc, hyps, f, a.add.b, b.add.a)))
        {
            return true;
        }
    }
    if (b.* == .add and (proveLe(alloc, hyps, f, a, b.add.a) or proveLe(alloc, hyps, f, a, b.add.b))) return true;
    if (a.* == .add) {
        const l = a.add.a;
        const r = a.add.b;
        if (l.* == .sub and r.eql(l.sub.b) and proveLe(alloc, hyps, f, l.sub.b, l.sub.a) and proveLe(alloc, hyps, f, l.sub.a, b)) return true;
        if (r.* == .sub and l.eql(r.sub.b) and proveLe(alloc, hyps, f, r.sub.b, r.sub.a) and proveLe(alloc, hyps, f, r.sub.a, b)) return true;
    }
    if (b.* == .add) {
        const l = b.add.a;
        const r = b.add.b;
        if (l.* == .sub and r.eql(l.sub.b) and proveLe(alloc, hyps, f, l.sub.b, l.sub.a) and proveLe(alloc, hyps, f, a, l.sub.a)) return true;
        if (r.* == .sub and l.eql(r.sub.b) and proveLe(alloc, hyps, f, r.sub.b, r.sub.a) and proveLe(alloc, hyps, f, a, r.sub.a)) return true;
    }
    return false;
}

fn proveEq(alloc: std.mem.Allocator, hyps: []const *const LawProp, fuel: u32, a: *const LawExpr, b: *const LawExpr) bool {
    if (fuel == 0) return false;
    const f = fuel - 1;
    if (a.eql(b)) return true;
    for (hyps) |h| if (hypImpliesEq(a, b, h)) return true;
    if (linearEq(alloc, a, b)) return true;
    if (a.* == .add) {
        const l = a.add.a;
        const r = a.add.b;
        if (l.* == .sub and r.eql(l.sub.b) and proveLe(alloc, hyps, f, l.sub.b, l.sub.a) and proveEq(alloc, hyps, f, l.sub.a, b)) return true;
        if (r.* == .sub and l.eql(r.sub.b) and proveLe(alloc, hyps, f, r.sub.b, r.sub.a) and proveEq(alloc, hyps, f, r.sub.a, b)) return true;
    }
    if (b.* == .add) {
        const l = b.add.a;
        const r = b.add.b;
        if (l.* == .sub and r.eql(l.sub.b) and proveLe(alloc, hyps, f, l.sub.b, l.sub.a) and proveEq(alloc, hyps, f, a, l.sub.a)) return true;
        if (r.* == .sub and l.eql(r.sub.b) and proveLe(alloc, hyps, f, r.sub.b, r.sub.a) and proveEq(alloc, hyps, f, a, r.sub.a)) return true;
    }
    return proveLe(alloc, hyps, f, a, b) and proveLe(alloc, hyps, f, b, a);
}

fn proveLt(alloc: std.mem.Allocator, hyps: []const *const LawProp, fuel: u32, a: *const LawExpr, b: *const LawExpr) bool {
    if (fuel == 0) return false;
    const f = fuel - 1;
    for (hyps) |h| if (hypImpliesLt(a, b, h)) return true;
    if (linearLt(alloc, a, b)) return true;
    const a_plus_1 = mkLawExpr(alloc, .{ .add = .{ .a = a, .b = mkLawExpr(alloc, .{ .const_val = 1 }) } });
    if (proveLe(alloc, hyps, f, a_plus_1, b)) return true;
    const zero = mkLawExpr(alloc, .{ .const_val = 0 });
    if (b.* == .add) {
        if ((proveLe(alloc, hyps, f, a, b.add.a) and proveLt(alloc, hyps, f, zero, b.add.b)) or
            (proveLe(alloc, hyps, f, a, b.add.b) and proveLt(alloc, hyps, f, zero, b.add.a)) or
            proveLt(alloc, hyps, f, a, b.add.a) or
            proveLt(alloc, hyps, f, a, b.add.b))
        {
            return true;
        }
    }
    if (a.* == .sub and b.* == .sub) {
        if (proveLe(alloc, hyps, f, a.sub.a, b.sub.a) and
            proveLt(alloc, hyps, f, b.sub.b, b.sub.a) and
            proveLt(alloc, hyps, f, b.sub.b, a.sub.b))
        {
            return true;
        }
        if (proveLt(alloc, hyps, f, zero, a.sub.a) and
            proveLt(alloc, hyps, f, zero, a.sub.b) and
            proveLe(alloc, hyps, f, a.sub.a, b))
        {
            return true;
        }
    }
    if (a.* == .sub) {
        if (proveLt(alloc, hyps, f, zero, a.sub.a) and
            proveLt(alloc, hyps, f, zero, a.sub.b) and
            proveLe(alloc, hyps, f, a.sub.a, b))
        {
            return true;
        }
    }
    return false;
}

fn flattenHyp(alloc: std.mem.Allocator, p: *const LawProp, out: *std.ArrayList(*const LawProp)) std.mem.Allocator.Error!void {
    switch (p.*) {
        .tt => {},
        .and_op => |pp| {
            try flattenHyp(alloc, pp.p, out);
            try flattenHyp(alloc, pp.q, out);
        },
        .not => |inner| switch (inner.*) {
            .lt => |ep| try out.append(alloc, mkLawProp(alloc, .{ .le = .{
                .a = normalizeLawExpr(alloc, ep.b),
                .b = normalizeLawExpr(alloc, ep.a),
            } })),
            .le => |ep| try out.append(alloc, mkLawProp(alloc, .{ .lt = .{
                .a = normalizeLawExpr(alloc, ep.b),
                .b = normalizeLawExpr(alloc, ep.a),
            } })),
            .not => |nn| try flattenHyp(alloc, nn, out),
            else => try out.append(alloc, p),
        },
        .eq => |ep| try out.append(alloc, mkLawProp(alloc, .{ .eq = .{
            .a = normalizeLawExpr(alloc, ep.a),
            .b = normalizeLawExpr(alloc, ep.b),
        } })),
        .le => |ep| try out.append(alloc, mkLawProp(alloc, .{ .le = .{
            .a = normalizeLawExpr(alloc, ep.a),
            .b = normalizeLawExpr(alloc, ep.b),
        } })),
        .lt => |ep| try out.append(alloc, mkLawProp(alloc, .{ .lt = .{
            .a = normalizeLawExpr(alloc, ep.a),
            .b = normalizeLawExpr(alloc, ep.b),
        } })),
        .ne => |ep| {
            const na = normalizeLawExpr(alloc, ep.a);
            const nb = normalizeLawExpr(alloc, ep.b);
            try out.append(alloc, mkLawProp(alloc, .{ .ne = .{ .a = na, .b = nb } }));
            const zero = mkLawExpr(alloc, .{ .const_val = 0 });
            if (na.* == .const_val and na.const_val == 0) {
                try out.append(alloc, mkLawProp(alloc, .{ .lt = .{ .a = zero, .b = nb } }));
            } else if (nb.* == .const_val and nb.const_val == 0) {
                try out.append(alloc, mkLawProp(alloc, .{ .lt = .{ .a = zero, .b = na } }));
            }
        },
        else => try out.append(alloc, p),
    }
}

fn autoProve(alloc: std.mem.Allocator, hyps: []const *const LawProp, fuel: u32, goal: *const LawProp) bool {
    if (fuel == 0) return false;
    const f = fuel - 1;
    switch (goal.*) {
        .tt => return true,
        .ff => {
            for (hyps) |h| if (h.* == .ff) return true;
            return false;
        },
        .eq => |ep| return proveEq(alloc, hyps, f, normalizeLawExpr(alloc, ep.a), normalizeLawExpr(alloc, ep.b)),
        .ne => |ep| {
            const a = normalizeLawExpr(alloc, ep.a);
            const b = normalizeLawExpr(alloc, ep.b);
            if (proveLt(alloc, hyps, f, a, b) or proveLt(alloc, hyps, f, b, a)) return true;
            for (hyps) |h| if (hypImpliesNe(a, b, h)) return true;
            return false;
        },
        .le => |ep| return proveLe(alloc, hyps, f, normalizeLawExpr(alloc, ep.a), normalizeLawExpr(alloc, ep.b)),
        .lt => |ep| return proveLt(alloc, hyps, f, normalizeLawExpr(alloc, ep.a), normalizeLawExpr(alloc, ep.b)),
        .not => |inner| switch (inner.*) {
            .lt => |ep| return proveLe(alloc, hyps, f, normalizeLawExpr(alloc, ep.b), normalizeLawExpr(alloc, ep.a)),
            .le => |ep| return proveLt(alloc, hyps, f, normalizeLawExpr(alloc, ep.b), normalizeLawExpr(alloc, ep.a)),
            .eq => |ep| return autoProve(alloc, hyps, f, mkLawProp(alloc, .{ .ne = ep })),
            .ne => |ep| return autoProve(alloc, hyps, f, mkLawProp(alloc, .{ .eq = ep })),
            .ff => return true,
            .not => |nn| return autoProve(alloc, hyps, f, nn),
            else => return false,
        },
        .and_op => |pp| return autoProve(alloc, hyps, f, pp.p) and autoProve(alloc, hyps, f, pp.q),
        .or_op => |pp| return autoProve(alloc, hyps, f, pp.p) or autoProve(alloc, hyps, f, pp.q),
        .imp => |pp| {
            var ext: std.ArrayList(*const LawProp) = .empty;
            flattenHyp(alloc, pp.p, &ext) catch return false;
            ext.appendSlice(alloc, hyps) catch return false;
            return autoProve(alloc, ext.items, f, pp.q);
        },
    }
}

pub fn autoProveNorm(alloc: std.mem.Allocator, hyps: []const *const LawProp, fuel: u32, goal: *const LawProp) bool {
    var flat: std.ArrayList(*const LawProp) = .empty;
    for (hyps) |h| flattenHyp(alloc, h, &flat) catch return false;
    return autoProve(alloc, flat.items, fuel, goal);
}

// =========================================================================
// Aethel AST <-> Symbolic & Concrete Verification Bridge
// =========================================================================

pub const ParamFieldInfo = struct {
    name: []const u8,
    int_ty: ?int_range.IntType,
    range: ?int_range.IntRange,
    is_bool: bool,
};

pub const LawParamDomain = struct {
    name: []const u8,
    kind: Kind,

    pub const Kind = union(enum) {
        bool_ty,
        int_ty: struct {
            int_ty: int_range.IntType,
            range: ?int_range.IntRange,
        },
        record_ty: struct {
            record_name: []const u8,
            fields: []const ParamFieldInfo,
        },
        enum_ty: struct {
            adt_name: []const u8,
            variant_count: usize,
        },
        other,
    };
};

pub const FnAstEntry = struct {
    name: []const u8,
    params: []const ast.Param,
    body: ast.Block,
};

pub const RecordFieldRuntime = struct {
    name: []const u8,
    int_ty: ?int_range.IntType,
    is_bool: bool,
};

pub const RecordAstInfo = struct {
    name: []const u8,
    fields: []const RecordFieldRuntime,
};

pub const VarSlot = struct {
    key: []const u8,
    id: u16,
    non_negative: bool,
};

pub const SymCtx = struct {
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    fns: []const FnAstEntry,
    resolved_calls: ?*const std.AutoHashMapUnmanaged(*const ast.Expr, []const u8) = null,
    vars: std.ArrayList(VarSlot) = .empty,
    subst: std.StringHashMapUnmanaged(*const LawExpr) = .empty,
    inline_depth: u8 = 0,

    pub fn bindVar(self: *SymCtx, key: []const u8, non_negative: bool) ?u16 {
        for (self.vars.items) |v| {
            if (std.mem.eql(u8, v.key, key)) {
                return if (v.non_negative) v.id else null;
            }
        }
        if (!non_negative) return null;
        const id: u16 = @intCast(self.vars.items.len);
        self.vars.append(self.alloc, .{ .key = key, .id = id, .non_negative = non_negative }) catch return null;
        return id;
    }

    pub fn lookupOrReject(self: *SymCtx, key: []const u8) ?*const LawExpr {
        if (self.subst.get(key)) |bound| return bound;
        for (self.vars.items) |v| {
            if (std.mem.eql(u8, v.key, key)) {
                return if (v.non_negative) mkLawExpr(self.alloc, .{ .var_id = v.id }) else null;
            }
        }
        return null;
    }
};

fn keyForPathExpr(alloc: std.mem.Allocator, source: [:0]const u8, expr: *const ast.Expr) ?[]const u8 {
    return switch (expr.*) {
        .ident => |sp| sp.slice(source),
        .field => |fld| blk: {
            const base = keyForPathExpr(alloc, source, fld.target) orelse return null;
            break :blk std.fmt.allocPrint(alloc, "{s}.{s}", .{ base, fld.name.slice(source) }) catch null;
        },
        else => null,
    };
}

pub fn astToLawExpr(ctx: *SymCtx, expr: *const ast.Expr) ?*const LawExpr {
    switch (expr.*) {
        .int_lit => |sp| {
            const parsed = int_range.parseIntLiteral(sp.slice(ctx.source)) orelse return null;
            if (parsed.value > std.math.maxInt(u64)) return null;
            return mkLawExpr(ctx.alloc, .{ .const_val = @intCast(parsed.value) });
        },
        .ident, .field => {
            const key = keyForPathExpr(ctx.alloc, ctx.source, expr) orelse return null;
            return ctx.lookupOrReject(key);
        },
        .cast => |c| return astToLawExpr(ctx, c.expr),
        .block => |blk| {
            var saved = std.ArrayList(struct { k: []const u8, prev: ?*const LawExpr }).empty;
            defer {
                for (saved.items) |item| {
                    if (item.prev) |p| {
                        ctx.subst.put(ctx.alloc, item.k, p) catch {};
                    } else {
                        _ = ctx.subst.remove(item.k);
                    }
                }
            }
            for (blk.stmts) |st| {
                if (st == .let_stmt and st.let_stmt.pattern.* == .ident) {
                    const lname = st.let_stmt.pattern.ident.name.slice(ctx.source);
                    const rhs = astToLawExpr(ctx, st.let_stmt.value) orelse return null;
                    saved.append(ctx.alloc, .{ .k = lname, .prev = ctx.subst.get(lname) }) catch return null;
                    ctx.subst.put(ctx.alloc, lname, rhs) catch return null;
                } else {
                    return null;
                }
            }
            if (blk.tail) |t| return astToLawExpr(ctx, t);
            return null;
        },
        .call => |c| {
            const cname = resolveLawCalleeName(ctx.source, c.callee, ctx.resolved_calls) orelse return null;
            if (std.mem.eql(u8, cname, "min") and c.args.len == 2) {
                const a = astToLawExpr(ctx, c.args[0].value) orelse return null;
                const b = astToLawExpr(ctx, c.args[1].value) orelse return null;
                return mkLawExpr(ctx.alloc, .{ .min = .{ .a = a, .b = b } });
            }
            if (std.mem.eql(u8, cname, "max") and c.args.len == 2) {
                const a = astToLawExpr(ctx, c.args[0].value) orelse return null;
                const b = astToLawExpr(ctx, c.args[1].value) orelse return null;
                return mkLawExpr(ctx.alloc, .{ .max = .{ .a = a, .b = b } });
            }
            if (ctx.inline_depth >= 4) return null;
            for (ctx.fns) |fn_entry| {
                if (!std.mem.eql(u8, fn_entry.name, cname)) continue;
                if (fn_entry.params.len != c.args.len) return null;
                var arg_vals = ctx.alloc.alloc(*const LawExpr, c.args.len) catch return null;
                for (c.args, 0..) |ca, ai| {
                    arg_vals[ai] = astToLawExpr(ctx, ca.value) orelse return null;
                }
                const saved_subst = ctx.subst;
                ctx.subst = .empty;
                for (fn_entry.params, 0..) |p, pi| {
                    ctx.subst.put(ctx.alloc, p.name.slice(ctx.source), arg_vals[pi]) catch {
                        ctx.subst = saved_subst;
                        return null;
                    };
                }
                ctx.inline_depth += 1;
                defer {
                    ctx.inline_depth -= 1;
                    ctx.subst = saved_subst;
                }
                if (fn_entry.body.stmts.len == 0 and fn_entry.body.tail != null) {
                    return astToLawExpr(ctx, fn_entry.body.tail.?);
                }
                const fake_blk = ast.Expr{ .block = fn_entry.body };
                return astToLawExpr(ctx, &fake_blk);
            }
            return null;
        },
        .binary => |b| {
            // IMPORTANT: Wrapping operators (+%, -%, *%) MUST NOT lower to Nat math!
            switch (b.op) {
                .add, .add_sat => {
                    const a = astToLawExpr(ctx, b.left) orelse return null;
                    const bv = astToLawExpr(ctx, b.right) orelse return null;
                    return mkLawExpr(ctx.alloc, .{ .add = .{ .a = a, .b = bv } });
                },
                .sub, .sub_sat => {
                    const a = astToLawExpr(ctx, b.left) orelse return null;
                    const bv = astToLawExpr(ctx, b.right) orelse return null;
                    return mkLawExpr(ctx.alloc, .{ .sub = .{ .a = a, .b = bv } });
                },
                .mul, .mul_sat => {
                    const a = astToLawExpr(ctx, b.left) orelse return null;
                    const bv = astToLawExpr(ctx, b.right) orelse return null;
                    if (a.* == .const_val) return mkLawExpr(ctx.alloc, .{ .mul_const = .{ .c = a.const_val, .e = bv } });
                    if (bv.* == .const_val) return mkLawExpr(ctx.alloc, .{ .mul_const = .{ .c = bv.const_val, .e = a } });
                    return null;
                },
                else => return null,
            }
        },
        else => return null,
    }
}

pub fn astToLawProp(ctx: *SymCtx, expr: *const ast.Expr) ?*const LawProp {
    switch (expr.*) {
        .bool_lit => |bl| return mkLawProp(ctx.alloc, if (bl.value) .tt else .ff),
        .unary => |u| {
            if (u.op == .not) {
                const inner = astToLawProp(ctx, u.operand) orelse return null;
                return mkLawProp(ctx.alloc, .{ .not = inner });
            }
            return null;
        },
        .binary => |b| {
            switch (b.op) {
                .and_op => {
                    const p = astToLawProp(ctx, b.left) orelse return null;
                    const q = astToLawProp(ctx, b.right) orelse return null;
                    return mkLawProp(ctx.alloc, .{ .and_op = .{ .p = p, .q = q } });
                },
                .or_op => {
                    const p = astToLawProp(ctx, b.left) orelse return null;
                    const q = astToLawProp(ctx, b.right) orelse return null;
                    return mkLawProp(ctx.alloc, .{ .or_op = .{ .p = p, .q = q } });
                },
                .eq, .ne, .le, .lt, .ge, .gt => {
                    const a = astToLawExpr(ctx, b.left) orelse return null;
                    const bv = astToLawExpr(ctx, b.right) orelse return null;
                    return switch (b.op) {
                        .eq => mkLawProp(ctx.alloc, .{ .eq = .{ .a = a, .b = bv } }),
                        .ne => mkLawProp(ctx.alloc, .{ .ne = .{ .a = a, .b = bv } }),
                        .le => mkLawProp(ctx.alloc, .{ .le = .{ .a = a, .b = bv } }),
                        .lt => mkLawProp(ctx.alloc, .{ .lt = .{ .a = a, .b = bv } }),
                        .ge => mkLawProp(ctx.alloc, .{ .le = .{ .a = bv, .b = a } }),
                        .gt => mkLawProp(ctx.alloc, .{ .lt = .{ .a = bv, .b = a } }),
                        else => unreachable,
                    };
                },
                else => return null,
            }
        },
        else => return null,
    }
}

pub fn tryProveSymbolicClause(
    alloc: std.mem.Allocator,
    ctx: *SymCtx,
    guard_exprs: []const *const ast.Expr,
    goal_expr: *const ast.Expr,
    is_never: bool,
) ?struct { hyps: []const *const LawProp, goal: *const LawProp } {
    var hyps: std.ArrayList(*const LawProp) = .empty;
    for (guard_exprs) |ge| {
        const gp = astToLawProp(ctx, ge) orelse return null;
        hyps.append(alloc, gp) catch return null;
    }
    const g_raw = astToLawProp(ctx, goal_expr) orelse return null;
    const goal = if (is_never) mkLawProp(alloc, .{ .not = g_raw }) else g_raw;
    if (autoProveNorm(alloc, hyps.items, 12, goal)) {
        return .{ .hyps = hyps.toOwnedSlice(alloc) catch return null, .goal = g_raw };
    }
    return null;
}

// =========================================================================
// Tier 1 Concrete Evaluator & Exhaustive / Bounded Falsifier
// =========================================================================

pub const ConcreteField = struct {
    name: []const u8,
    val: ConcreteVal,
    int_ty: ?int_range.IntType,
};

pub const ConcreteVal = union(enum) {
    int_val: struct {
        val: i128,
        int_ty: ?int_range.IntType,
    },
    bool_val: bool,
    enum_val: usize,
    record_val: []const ConcreteField,
    unit_val,
};

pub const ConcreteEnv = struct {
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    fns: []const FnAstEntry,
    records: []const RecordAstInfo,
    resolved_calls: ?*const std.AutoHashMapUnmanaged(*const ast.Expr, []const u8) = null,
    bindings: std.StringHashMapUnmanaged(ConcreteVal) = .empty,
    call_depth: u8 = 0,
};

fn resolveLawCalleeName(
    source: [:0]const u8,
    callee: *const ast.Expr,
    resolved_calls: ?*const std.AutoHashMapUnmanaged(*const ast.Expr, []const u8),
) ?[]const u8 {
    if (resolved_calls) |rc| {
        if (rc.get(callee)) |cname| return cname;
    }
    if (callee.* == .ident) return callee.ident.slice(source);
    return null;
}

fn wrapIntValue(v: i128, it: int_range.IntType) i128 {
    if (it.bits >= 127) return v;
    const modulus: i128 = @as(i128, 1) << @intCast(it.bits);
    if (!it.signed) {
        var r = @mod(v, modulus);
        if (r < 0) r += modulus;
        return r;
    }
    const half: i128 = @as(i128, 1) << @intCast(it.bits - 1);
    var r = @mod(v + half, modulus);
    if (r < 0) r += modulus;
    return r - half;
}

fn clampIntValue(v: i128, it: int_range.IntType) i128 {
    if (it.bits >= 127) return v;
    if (!it.signed) {
        const hi: i128 = (@as(i128, 1) << @intCast(it.bits)) - 1;
        return std.math.clamp(v, 0, hi);
    }
    const half: i128 = @as(i128, 1) << @intCast(it.bits - 1);
    return std.math.clamp(v, -half, half - 1);
}

fn intTypeFromAstType(source: [:0]const u8, te: ?*const ast.TypeExpr) ?int_range.IntType {
    const t = te orelse return null;
    return switch (t.*) {
        .primitive => |p| switch (p.prim) {
            .unsigned => |bits| .{ .signed = false, .bits = bits },
            .signed => |bits| .{ .signed = true, .bits = bits },
            else => null,
        },
        .int_range => |ir| blk: {
            if (ir.lo.* != .int_lit or ir.hi.* != .int_lit) break :blk null;
            const lo_p = int_range.parseIntLiteral(ir.lo.int_lit.slice(source)) orelse break :blk null;
            const hi_p = int_range.parseIntLiteral(ir.hi.int_lit.slice(source)) orelse break :blk null;
            if (lo_p.value <= std.math.maxInt(i128) and hi_p.value <= std.math.maxInt(i128)) {
                var hi_val: i128 = @intCast(hi_p.value);
                if (!ir.inclusive) hi_val -= 1;
                const rng = int_range.IntRange{ .bounded = .{ .lo = @intCast(lo_p.value), .hi = hi_val } };
                break :blk int_range.inferIntegerType(rng);
            }
            break :blk null;
        },
        else => null,
    };
}

pub fn evalConcreteExpr(env: *ConcreteEnv, expr: *const ast.Expr) ?ConcreteVal {
    switch (expr.*) {
        .int_lit => |sp| {
            const parsed = int_range.parseIntLiteral(sp.slice(env.source)) orelse return null;
            if (parsed.value > std.math.maxInt(i128)) return null;
            return .{ .int_val = .{ .val = @intCast(parsed.value), .int_ty = parsed.suffix } };
        },
        .bool_lit => |bl| return .{ .bool_val = bl.value },
        .ident => |sp| return env.bindings.get(sp.slice(env.source)),
        .upper_ident => |sp| {
            _ = sp;
            return null;
        },
        .cast => |c| {
            const inner = evalConcreteExpr(env, c.expr) orelse return null;
            const dst_it = intTypeFromAstType(env.source, c.ty) orelse return inner;
            if (inner == .int_val) {
                return .{ .int_val = .{ .val = wrapIntValue(inner.int_val.val, dst_it), .int_ty = dst_it } };
            }
            return inner;
        },
        .field => |fld| {
            const base = evalConcreteExpr(env, fld.target) orelse return null;
            if (base != .record_val) return null;
            const fname = fld.name.slice(env.source);
            for (base.record_val) |rf| {
                if (std.mem.eql(u8, rf.name, fname)) return rf.val;
            }
            return null;
        },
        .record_lit => |rl| {
            var fs = env.alloc.alloc(ConcreteField, rl.fields.len) catch return null;
            for (rl.fields, 0..) |rf, i| {
                const v = if (rf.value) |ve| evalConcreteExpr(env, ve) orelse return null else return null;
                fs[i] = .{
                    .name = rf.name.slice(env.source),
                    .val = v,
                    .int_ty = if (v == .int_val) v.int_val.int_ty else null,
                };
            }
            return .{ .record_val = fs };
        },
        .unary => |u| {
            const opv = evalConcreteExpr(env, u.operand) orelse return null;
            return switch (u.op) {
                .not => if (opv == .bool_val) .{ .bool_val = !opv.bool_val } else null,
                .neg => if (opv == .int_val) .{ .int_val = .{ .val = -opv.int_val.val, .int_ty = opv.int_val.int_ty } } else null,
                .bit_not => if (opv == .int_val) .{ .int_val = .{
                    .val = if (opv.int_val.int_ty) |it| wrapIntValue(~opv.int_val.val, it) else ~opv.int_val.val,
                    .int_ty = opv.int_val.int_ty,
                } } else null,
                else => null,
            };
        },
        .if_expr => |ie| {
            const cond = evalConcreteExpr(env, ie.cond) orelse return null;
            if (cond != .bool_val) return null;
            if (cond.bool_val) {
                const blk_e = ast.Expr{ .block = ie.then_block };
                return evalConcreteExpr(env, &blk_e);
            } else if (ie.else_branch) |eb| {
                return evalConcreteExpr(env, eb);
            }
            return .unit_val;
        },
        .block => |blk| {
            const saved = env.bindings;
            env.bindings = saved.clone(env.alloc) catch return null;
            defer env.bindings = saved;
            for (blk.stmts) |st| {
                switch (st) {
                    .let_stmt => |ls| {
                        if (ls.pattern.* != .ident) return null;
                        var v = evalConcreteExpr(env, ls.value) orelse return null;
                        if (v == .int_val) {
                            if (intTypeFromAstType(env.source, ls.ty)) |lt| {
                                v = .{ .int_val = .{ .val = v.int_val.val, .int_ty = lt } };
                            }
                        }
                        env.bindings.put(env.alloc, ls.pattern.ident.name.slice(env.source), v) catch return null;
                    },
                    .assign_stmt => |asg| {
                        if (asg.target.* != .ident) return null;
                        const nm = asg.target.ident.slice(env.source);
                        const cur = env.bindings.get(nm) orelse return null;
                        const rhs = evalConcreteExpr(env, asg.value) orelse return null;
                        if (asg.op == .assign) {
                            env.bindings.put(env.alloc, nm, rhs) catch return null;
                        } else if (cur == .int_val and rhs == .int_val) {
                            const nv: i128 = switch (asg.op) {
                                .add_assign => cur.int_val.val + rhs.int_val.val,
                                .sub_assign => cur.int_val.val - rhs.int_val.val,
                                .mul_assign => cur.int_val.val * rhs.int_val.val,
                                .div_assign => if (rhs.int_val.val != 0) @divTrunc(cur.int_val.val, rhs.int_val.val) else return null,
                                .rem_assign => if (rhs.int_val.val != 0) @rem(cur.int_val.val, rhs.int_val.val) else return null,
                                else => return null,
                            };
                            env.bindings.put(env.alloc, nm, .{ .int_val = .{ .val = nv, .int_ty = cur.int_val.int_ty } }) catch return null;
                        } else return null;
                    },
                    .return_stmt => |rs| {
                        if (rs.value) |rv| return evalConcreteExpr(env, rv);
                        return .unit_val;
                    },
                    else => return null,
                }
            }
            if (blk.tail) |t| return evalConcreteExpr(env, t);
            return .unit_val;
        },
        .call => |c| {
            const cname = resolveLawCalleeName(env.source, c.callee, env.resolved_calls) orelse return null;
            if (std.mem.eql(u8, cname, "min") and c.args.len == 2) {
                const a = evalConcreteExpr(env, c.args[0].value) orelse return null;
                const b = evalConcreteExpr(env, c.args[1].value) orelse return null;
                if (a != .int_val or b != .int_val) return null;
                return .{ .int_val = .{ .val = @min(a.int_val.val, b.int_val.val), .int_ty = a.int_val.int_ty orelse b.int_val.int_ty } };
            }
            if (std.mem.eql(u8, cname, "max") and c.args.len == 2) {
                const a = evalConcreteExpr(env, c.args[0].value) orelse return null;
                const b = evalConcreteExpr(env, c.args[1].value) orelse return null;
                if (a != .int_val or b != .int_val) return null;
                return .{ .int_val = .{ .val = @max(a.int_val.val, b.int_val.val), .int_ty = a.int_val.int_ty orelse b.int_val.int_ty } };
            }
            if (env.call_depth >= 12) return null;
            for (env.fns) |fn_entry| {
                if (!std.mem.eql(u8, fn_entry.name, cname)) continue;
                if (fn_entry.params.len != c.args.len) return null;
                var arg_vals = env.alloc.alloc(ConcreteVal, c.args.len) catch return null;
                for (c.args, 0..) |ca, ai| {
                    var av = evalConcreteExpr(env, ca.value) orelse return null;
                    if (av == .int_val and av.int_val.int_ty == null) {
                        av.int_val.int_ty = intTypeFromAstType(env.source, fn_entry.params[ai].ty);
                    }
                    arg_vals[ai] = av;
                }
                const saved = env.bindings;
                env.bindings = .empty;
                for (fn_entry.params, 0..) |p, pi| {
                    env.bindings.put(env.alloc, p.name.slice(env.source), arg_vals[pi]) catch {
                        env.bindings = saved;
                        return null;
                    };
                }
                env.call_depth += 1;
                defer {
                    env.call_depth -= 1;
                    env.bindings = saved;
                }
                const fake_blk = ast.Expr{ .block = fn_entry.body };
                return evalConcreteExpr(env, &fake_blk);
            }
            return null;
        },
        .binary => |b| {
            const lv = evalConcreteExpr(env, b.left) orelse return null;
            if (b.op == .and_op) {
                if (lv != .bool_val) return null;
                if (!lv.bool_val) return .{ .bool_val = false };
                const rv = evalConcreteExpr(env, b.right) orelse return null;
                return if (rv == .bool_val) rv else null;
            }
            if (b.op == .or_op) {
                if (lv != .bool_val) return null;
                if (lv.bool_val) return .{ .bool_val = true };
                const rv = evalConcreteExpr(env, b.right) orelse return null;
                return if (rv == .bool_val) rv else null;
            }
            const rv = evalConcreteExpr(env, b.right) orelse return null;
            if (lv == .bool_val and rv == .bool_val) {
                return switch (b.op) {
                    .eq => .{ .bool_val = lv.bool_val == rv.bool_val },
                    .ne => .{ .bool_val = lv.bool_val != rv.bool_val },
                    else => null,
                };
            }
            if (lv != .int_val or rv != .int_val) return null;
            const a = lv.int_val.val;
            const bv = rv.int_val.val;
            const common_ty = lv.int_val.int_ty orelse rv.int_val.int_ty;
            return switch (b.op) {
                .eq => .{ .bool_val = a == bv },
                .ne => .{ .bool_val = a != bv },
                .lt => .{ .bool_val = a < bv },
                .le => .{ .bool_val = a <= bv },
                .gt => .{ .bool_val = a > bv },
                .ge => .{ .bool_val = a >= bv },
                .add => .{ .int_val = .{ .val = a + bv, .int_ty = common_ty } },
                .sub => .{ .int_val = .{ .val = a - bv, .int_ty = common_ty } },
                .mul => .{ .int_val = .{ .val = a * bv, .int_ty = common_ty } },
                .div => if (bv != 0) .{ .int_val = .{ .val = @divTrunc(a, bv), .int_ty = common_ty } } else null,
                .rem => if (bv != 0) .{ .int_val = .{ .val = @rem(a, bv), .int_ty = common_ty } } else null,
                .add_wrap => .{ .int_val = .{ .val = if (common_ty) |it| wrapIntValue(a + bv, it) else a + bv, .int_ty = common_ty } },
                .sub_wrap => .{ .int_val = .{ .val = if (common_ty) |it| wrapIntValue(a - bv, it) else a - bv, .int_ty = common_ty } },
                .mul_wrap => .{ .int_val = .{ .val = if (common_ty) |it| wrapIntValue(a * bv, it) else a * bv, .int_ty = common_ty } },
                .add_sat => .{ .int_val = .{ .val = if (common_ty) |it| clampIntValue(a + bv, it) else a + bv, .int_ty = common_ty } },
                .sub_sat => .{ .int_val = .{ .val = if (common_ty) |it| clampIntValue(a - bv, it) else @max(@as(i128, 0), a - bv), .int_ty = common_ty } },
                .mul_sat => .{ .int_val = .{ .val = if (common_ty) |it| clampIntValue(a * bv, it) else a * bv, .int_ty = common_ty } },
                .bit_and => .{ .int_val = .{ .val = a & bv, .int_ty = common_ty } },
                .bit_or => .{ .int_val = .{ .val = a | bv, .int_ty = common_ty } },
                .bit_xor => .{ .int_val = .{ .val = a ^ bv, .int_ty = common_ty } },
                else => null,
            };
        },
        else => return null,
    }
}

pub const Tier1Outcome = union(enum) {
    proved_exhaustive: usize,
    falsified: []const u8,
    inconclusive,
};

fn buildCandidatesForInt(
    alloc: std.mem.Allocator,
    it: int_range.IntType,
    rng: ?int_range.IntRange,
    exhaustive: bool,
) ?[]const ConcreteVal {
    var lo: i128 = 0;
    var hi: i128 = 0;
    if (rng != null and rng.? == .bounded) {
        lo = rng.?.bounded.lo;
        hi = rng.?.bounded.hi;
    } else if (it.bits <= 16) {
        if (it.signed) {
            const half: i128 = @as(i128, 1) << @intCast(it.bits - 1);
            lo = -half;
            hi = half - 1;
        } else {
            lo = 0;
            hi = (@as(i128, 1) << @intCast(it.bits)) - 1;
        }
    } else {
        if (it.signed) {
            lo = -(@as(i128, 1) << 31);
            hi = (@as(i128, 1) << 31) - 1;
        } else {
            lo = 0;
            hi = (@as(i128, 1) << 32) - 1;
        }
    }
    if (exhaustive) {
        if (hi < lo) return &.{};
        const span = hi - lo + 1;
        if (span > 256) return null;
        var vals = alloc.alloc(ConcreteVal, @intCast(span)) catch return null;
        var cur = lo;
        var idx: usize = 0;
        while (cur <= hi) : ({
            cur += 1;
            idx += 1;
        }) {
            vals[idx] = .{ .int_val = .{ .val = cur, .int_ty = it } };
        }
        return vals;
    }
    var list: std.ArrayList(ConcreteVal) = .empty;
    const raw_samples = [_]i128{ lo, lo + 1, -2, -1, 0, 1, 2, 3, 5, 10, 42, 100, hi - 1, hi };
    for (raw_samples) |s| {
        if (s < lo or s > hi) continue;
        var dup = false;
        for (list.items) |prev| if (prev.int_val.val == s) {
            dup = true;
            break;
        };
        if (!dup) list.append(alloc, .{ .int_val = .{ .val = s, .int_ty = it } }) catch return null;
    }
    return list.toOwnedSlice(alloc) catch return null;
}

fn buildParamCandidates(alloc: std.mem.Allocator, dom: LawParamDomain, exhaustive: bool) ?[]const ConcreteVal {
    switch (dom.kind) {
        .bool_ty => {
            var vals = alloc.alloc(ConcreteVal, 2) catch return null;
            vals[0] = .{ .bool_val = false };
            vals[1] = .{ .bool_val = true };
            return vals;
        },
        .int_ty => |ii| {
            if (exhaustive) {
                const fits_small = (ii.range != null and ii.range.? == .bounded and
                    (ii.range.?.bounded.hi - ii.range.?.bounded.lo + 1) <= 256) or ii.int_ty.bits <= 8;
                if (!fits_small) return null;
            }
            return buildCandidatesForInt(alloc, ii.int_ty, ii.range, exhaustive);
        },
        .enum_ty => |et| {
            if (et.variant_count == 0 or et.variant_count > 64) return null;
            var vals = alloc.alloc(ConcreteVal, et.variant_count) catch return null;
            for (0..et.variant_count) |vi| vals[vi] = .{ .enum_val = vi };
            return vals;
        },
        .record_ty => |rt| {
            if (rt.fields.len == 0 or rt.fields.len > 6) return null;
            var field_cands: [6][]const ConcreteVal = undefined;
            var total: usize = 1;
            for (rt.fields, 0..) |rf, fi| {
                const sub_dom = LawParamDomain{
                    .name = rf.name,
                    .kind = if (rf.is_bool) .bool_ty else if (rf.int_ty) |it| .{ .int_ty = .{ .int_ty = it, .range = rf.range } } else return null,
                };
                const cs = buildParamCandidates(alloc, sub_dom, exhaustive) orelse return null;
                if (cs.len == 0) return null;
                const next_total = std.math.mul(usize, total, cs.len) catch return null;
                if (exhaustive and next_total > 1024) return null;
                if (!exhaustive and next_total > 256) return null;
                total = next_total;
                field_cands[fi] = cs;
            }
            var recs = alloc.alloc(ConcreteVal, total) catch return null;
            var idxs: [6]usize = @splat(0);
            for (0..total) |ri| {
                var fvals = alloc.alloc(ConcreteField, rt.fields.len) catch return null;
                for (rt.fields, 0..) |rf, fi| {
                    const cv = field_cands[fi][idxs[fi]];
                    fvals[fi] = .{ .name = rf.name, .val = cv, .int_ty = if (cv == .int_val) cv.int_val.int_ty else null };
                }
                recs[ri] = .{ .record_val = fvals };
                var carry = rt.fields.len;
                while (carry > 0) {
                    carry -= 1;
                    idxs[carry] += 1;
                    if (idxs[carry] < field_cands[carry].len) break;
                    idxs[carry] = 0;
                }
            }
            return recs;
        },
        .other => return null,
    }
}

fn formatConcreteVal(alloc: std.mem.Allocator, val: ConcreteVal) []const u8 {
    return switch (val) {
        .bool_val => |b| if (b) "true" else "false",
        .int_val => |iv| std.fmt.allocPrint(alloc, "{d}", .{iv.val}) catch "?",
        .enum_val => |ev| std.fmt.allocPrint(alloc, "#{d}", .{ev}) catch "?",
        .record_val => |fs| blk: {
            var buf: std.ArrayList(u8) = .empty;
            buf.appendSlice(alloc, "{") catch return "{...}";
            for (fs, 0..) |rf, i| {
                if (i > 0) buf.appendSlice(alloc, ", ") catch {};
                buf.appendSlice(alloc, rf.name) catch {};
                buf.appendSlice(alloc, ": ") catch {};
                buf.appendSlice(alloc, formatConcreteVal(alloc, rf.val)) catch {};
            }
            buf.append(alloc, '}') catch {};
            break :blk buf.toOwnedSlice(alloc) catch "{...}";
        },
        .unit_val => "()",
    };
}

fn checkConcreteClause(
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    fns: []const FnAstEntry,
    records: []const RecordAstInfo,
    resolved_calls: ?*const std.AutoHashMapUnmanaged(*const ast.Expr, []const u8),
    params: []const LawParamDomain,
    guards: []const *const ast.Expr,
    goal: *const ast.Expr,
    is_never: bool,
    exhaustive: bool,
    max_states: usize,
) Tier1Outcome {
    if (params.len == 0 or params.len > 12) return .inconclusive;
    var cand_lists: [12][]const ConcreteVal = undefined;
    var total: usize = 1;
    for (params, 0..) |p, pi| {
        const cs = buildParamCandidates(alloc, p, exhaustive) orelse return .inconclusive;
        if (cs.len == 0) return .inconclusive;
        cand_lists[pi] = cs;
        total = std.math.mul(usize, total, cs.len) catch std.math.maxInt(usize);
        if (exhaustive and total > max_states) return .inconclusive;
    }

    const limit = if (exhaustive) total else @min(total, max_states);
    var idxs: [12]usize = @splat(0);
    var tested: usize = 0;

    var env = ConcreteEnv{
        .alloc = alloc,
        .source = source,
        .fns = fns,
        .records = records,
        .resolved_calls = resolved_calls,
    };

    var eval_ok = true;
    while (tested < limit) : (tested += 1) {
        env.bindings = .empty;
        for (params, 0..) |p, pi| {
            env.bindings.put(alloc, p.name, cand_lists[pi][idxs[pi]]) catch return .inconclusive;
        }

        var guards_hold = true;
        for (guards) |ge| {
            const gv = evalConcreteExpr(&env, ge) orelse {
                eval_ok = false;
                break;
            };
            if (gv != .bool_val) {
                eval_ok = false;
                break;
            }
            if (!gv.bool_val) {
                guards_hold = false;
                break;
            }
        }
        if (!eval_ok) break;

        if (guards_hold) {
            const rv = evalConcreteExpr(&env, goal) orelse {
                eval_ok = false;
                break;
            };
            if (rv != .bool_val) {
                eval_ok = false;
                break;
            }
            const passed = if (is_never) !rv.bool_val else rv.bool_val;
            if (!passed) {
                var msg: std.ArrayList(u8) = .empty;
                for (params, 0..) |p, pi| {
                    if (pi > 0) msg.appendSlice(alloc, ", ") catch {};
                    msg.appendSlice(alloc, p.name) catch {};
                    msg.appendSlice(alloc, " = ") catch {};
                    msg.appendSlice(alloc, formatConcreteVal(alloc, cand_lists[pi][idxs[pi]])) catch {};
                }
                return .{ .falsified = msg.toOwnedSlice(alloc) catch "counterexample found" };
            }
        }

        var carry = params.len;
        while (carry > 0) {
            carry -= 1;
            idxs[carry] += 1;
            if (idxs[carry] < cand_lists[carry].len) break;
            idxs[carry] = 0;
        }
    }
    if (!eval_ok) return .inconclusive;
    if (exhaustive) return .{ .proved_exhaustive = tested };
    return .inconclusive;
}

pub fn runTier1Clause(
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    fns: []const FnAstEntry,
    records: []const RecordAstInfo,
    params: []const LawParamDomain,
    guards: []const *const ast.Expr,
    goal: *const ast.Expr,
    is_never: bool,
) Tier1Outcome {
    return runTier1ClauseResolved(alloc, source, fns, records, null, params, guards, goal, is_never);
}

pub fn runTier1ClauseResolved(
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    fns: []const FnAstEntry,
    records: []const RecordAstInfo,
    resolved_calls: ?*const std.AutoHashMapUnmanaged(*const ast.Expr, []const u8),
    params: []const LawParamDomain,
    guards: []const *const ast.Expr,
    goal: *const ast.Expr,
    is_never: bool,
) Tier1Outcome {
    const exh = checkConcreteClause(alloc, source, fns, records, resolved_calls, params, guards, goal, is_never, true, 65536);
    if (exh != .inconclusive) return exh;
    return checkConcreteClause(alloc, source, fns, records, resolved_calls, params, guards, goal, is_never, false, 4096);
}

pub fn runTier1BoundedFalsify(
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    fns: []const FnAstEntry,
    records: []const RecordAstInfo,
    params: []const LawParamDomain,
    guards: []const *const ast.Expr,
    goal: *const ast.Expr,
    is_never: bool,
) ?[]const u8 {
    return switch (checkConcreteClause(alloc, source, fns, records, null, params, guards, goal, is_never, false, 4096)) {
        .falsified => |w| w,
        else => null,
    };
}

// =========================================================================
// Termination `decreases` Symbolic Proof & Substitution Helpers
// =========================================================================

pub const SymBinding = struct {
    name: []const u8,
    non_negative: bool,
    min_lower_bound: ?u64,
};

fn substLawExpr(alloc: std.mem.Allocator, expr: *const LawExpr, mapping: *const std.AutoHashMapUnmanaged(u16, *const LawExpr)) *const LawExpr {
    return switch (expr.*) {
        .var_id => |id| mapping.get(id) orelse expr,
        .const_val => expr,
        .add => |p| mkLawExpr(alloc, .{ .add = .{ .a = substLawExpr(alloc, p.a, mapping), .b = substLawExpr(alloc, p.b, mapping) } }),
        .sub => |p| mkLawExpr(alloc, .{ .sub = .{ .a = substLawExpr(alloc, p.a, mapping), .b = substLawExpr(alloc, p.b, mapping) } }),
        .mul_const => |mc| mkLawExpr(alloc, .{ .mul_const = .{ .c = mc.c, .e = substLawExpr(alloc, mc.e, mapping) } }),
        .min => |p| mkLawExpr(alloc, .{ .min = .{ .a = substLawExpr(alloc, p.a, mapping), .b = substLawExpr(alloc, p.b, mapping) } }),
        .max => |p| mkLawExpr(alloc, .{ .max = .{ .a = substLawExpr(alloc, p.a, mapping), .b = substLawExpr(alloc, p.b, mapping) } }),
    };
}

fn initSymCtxFromBindings(
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    fns: []const FnAstEntry,
    bindings: []const SymBinding,
) struct { ctx: SymCtx, guards: std.ArrayList(*const LawProp) } {
    var ctx = SymCtx{ .alloc = alloc, .source = source, .fns = fns };
    var guards: std.ArrayList(*const LawProp) = .empty;
    for (bindings) |b| {
        if (ctx.bindVar(b.name, b.non_negative)) |vid| {
            if (b.min_lower_bound) |lb| {
                if (lb > 0) {
                    const zero = mkLawExpr(alloc, .{ .const_val = 0 });
                    const v = mkLawExpr(alloc, .{ .var_id = vid });
                    guards.append(alloc, mkLawProp(alloc, .{ .lt = .{ .a = zero, .b = v } })) catch {};
                    if (lb > 1) {
                        const c = mkLawExpr(alloc, .{ .const_val = lb });
                        guards.append(alloc, mkLawProp(alloc, .{ .le = .{ .a = c, .b = v } })) catch {};
                    }
                }
            }
        }
    }
    return .{ .ctx = ctx, .guards = guards };
}

pub const DecreasesResult = union(enum) {
    proved: DecreasesCertEmit,
    failed: []const u8,
};

fn substLawExprChecked(alloc: std.mem.Allocator, expr: *const LawExpr, mapping: *const std.AutoHashMapUnmanaged(u16, ?*const LawExpr)) ?*const LawExpr {
    return switch (expr.*) {
        .var_id => |id| if (mapping.get(id)) |opt| opt else expr,
        .const_val => expr,
        .add => |p| mkLawExpr(alloc, .{ .add = .{
            .a = substLawExprChecked(alloc, p.a, mapping) orelse return null,
            .b = substLawExprChecked(alloc, p.b, mapping) orelse return null,
        } }),
        .sub => |p| mkLawExpr(alloc, .{ .sub = .{
            .a = substLawExprChecked(alloc, p.a, mapping) orelse return null,
            .b = substLawExprChecked(alloc, p.b, mapping) orelse return null,
        } }),
        .mul_const => |mc| mkLawExpr(alloc, .{ .mul_const = .{
            .c = mc.c,
            .e = substLawExprChecked(alloc, mc.e, mapping) orelse return null,
        } }),
        .min => |p| mkLawExpr(alloc, .{ .min = .{
            .a = substLawExprChecked(alloc, p.a, mapping) orelse return null,
            .b = substLawExprChecked(alloc, p.b, mapping) orelse return null,
        } }),
        .max => |p| mkLawExpr(alloc, .{ .max = .{
            .a = substLawExprChecked(alloc, p.a, mapping) orelse return null,
            .b = substLawExprChecked(alloc, p.b, mapping) orelse return null,
        } }),
    };
}

pub fn verifyWhileDecreases(
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    fns: []const FnAstEntry,
    cond_expr: *const ast.Expr,
    dec_expr: *const ast.Expr,
    body: ast.Block,
    bindings: []const SymBinding,
) DecreasesResult {
    var st = initSymCtxFromBindings(alloc, source, fns, bindings);
    const cond_prop = astToLawProp(&st.ctx, cond_expr) orelse {
        return .{ .failed = "while condition is outside decidable Nat termination fragment" };
    };
    st.guards.append(alloc, cond_prop) catch {};

    const cur_measure = astToLawExpr(&st.ctx, dec_expr) orelse {
        return .{ .failed = "while 'decreases' measure is outside decidable Nat expression fragment" };
    };

    var var_updates: std.AutoHashMapUnmanaged(u16, ?*const LawExpr) = .empty;
    for (body.stmts) |stmt| {
        if (stmt == .let_stmt and stmt.let_stmt.pattern.* == .ident) {
            const ls = stmt.let_stmt;
            const lname = ls.pattern.ident.name.slice(source);
            const saved_subst = st.ctx.subst;
            st.ctx.subst = saved_subst.clone(alloc) catch saved_subst;
            var it = var_updates.iterator();
            while (it.next()) |entry| {
                if (entry.value_ptr.*) |val| {
                    for (st.ctx.vars.items) |sv| {
                        if (sv.id == entry.key_ptr.*) {
                            st.ctx.subst.put(alloc, sv.key, val) catch {};
                        }
                    }
                }
            }
            const rhs_opt = astToLawExpr(&st.ctx, ls.value);
            st.ctx.subst = saved_subst;
            if (rhs_opt) |rhs_expr| {
                st.ctx.subst.put(alloc, lname, rhs_expr) catch {};
            }
        } else if (stmt == .assign_stmt) {
            const asg = stmt.assign_stmt;
            if (asg.target.* != .ident) continue;
            const vname = asg.target.ident.slice(source);
            const cur_lhs = st.ctx.lookupOrReject(vname) orelse continue;
            const vid = cur_lhs.var_id;
            const mapped_cur: ?*const LawExpr = if (var_updates.get(vid)) |opt| opt else cur_lhs;

            const saved_subst = st.ctx.subst;
            st.ctx.subst = saved_subst.clone(alloc) catch saved_subst;
            defer st.ctx.subst = saved_subst;
            var it = var_updates.iterator();
            while (it.next()) |entry| {
                if (entry.value_ptr.*) |val| {
                    for (st.ctx.vars.items) |sv| {
                        if (sv.id == entry.key_ptr.*) {
                            st.ctx.subst.put(alloc, sv.key, val) catch {};
                        }
                    }
                } else {
                    for (st.ctx.vars.items) |sv| {
                        if (sv.id == entry.key_ptr.*) {
                            _ = st.ctx.subst.remove(sv.key);
                        }
                    }
                }
            }

            const rhs_expr = astToLawExpr(&st.ctx, asg.value) orelse {
                var_updates.put(alloc, vid, null) catch {};
                continue;
            };
            const next_val: ?*const LawExpr = switch (asg.op) {
                .assign => rhs_expr,
                .add_assign => if (mapped_cur) |mc| mkLawExpr(alloc, .{ .add = .{ .a = mc, .b = rhs_expr } }) else null,
                .sub_assign => if (mapped_cur) |mc| mkLawExpr(alloc, .{ .sub = .{ .a = mc, .b = rhs_expr } }) else null,
                else => null,
            };
            var_updates.put(alloc, vid, next_val) catch {};
        } else if (stmt == .while_stmt) {
            return .{ .failed = "nested while loops require separate measure preservation proof" };
        }
    }

    const next_measure = substLawExprChecked(alloc, cur_measure, &var_updates) orelse {
        return .{ .failed = "while loop mutates 'decreases' measure variable outside decidable Nat fragment" };
    };
    const goal = mkLawProp(alloc, .{ .lt = .{ .a = next_measure, .b = cur_measure } });
    if (autoProveNorm(alloc, st.guards.items, 12, goal)) {
        return .{ .proved = .{
            .guards = st.guards.toOwnedSlice(alloc) catch &.{},
            .cur_measure = cur_measure,
            .next_measure = next_measure,
        } };
    }
    return .{ .failed = "cannot prove loop 'decreases' measure strictly decreases on every iteration" };
}

pub fn verifyRecursiveCallDecreases(
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    fns: []const FnAstEntry,
    guard_exprs: []const *const ast.Expr,
    dec_expr: *const ast.Expr,
    param_names: []const []const u8,
    arg_exprs: []const *const ast.Expr,
    bindings: []const SymBinding,
) DecreasesResult {
    if (param_names.len != arg_exprs.len) {
        return .{ .failed = "recursive call arity mismatch for 'decreases' termination check" };
    }
    var st = initSymCtxFromBindings(alloc, source, fns, bindings);
    for (guard_exprs) |ge| {
        if (astToLawProp(&st.ctx, ge)) |gp| {
            st.guards.append(alloc, gp) catch {};
        }
    }

    const cur_measure = astToLawExpr(&st.ctx, dec_expr) orelse {
        return .{ .failed = "function 'decreases' measure is outside decidable Nat expression fragment" };
    };

    var arg_updates: std.AutoHashMapUnmanaged(u16, *const LawExpr) = .empty;
    for (param_names, 0..) |pname, pi| {
        const param_sym = st.ctx.lookupOrReject(pname) orelse continue;
        const arg_sym = astToLawExpr(&st.ctx, arg_exprs[pi]) orelse {
            return .{ .failed = "recursive call argument is outside decidable Nat termination fragment" };
        };
        arg_updates.put(alloc, param_sym.var_id, arg_sym) catch {};
    }

    const next_measure = substLawExpr(alloc, cur_measure, &arg_updates);
    const goal = mkLawProp(alloc, .{ .lt = .{ .a = next_measure, .b = cur_measure } });
    if (autoProveNorm(alloc, st.guards.items, 12, goal)) {
        return .{ .proved = .{
            .guards = st.guards.toOwnedSlice(alloc) catch &.{},
            .cur_measure = cur_measure,
            .next_measure = next_measure,
        } };
    }
    return .{ .failed = "recursive call does not strictly decrease 'decreases' measure under active branch guards" };
}
