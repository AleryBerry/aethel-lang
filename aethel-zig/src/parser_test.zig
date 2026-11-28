const std = @import("std");
const ast = @import("ast.zig");
const parser = @import("parser.zig");

fn parseOk(source: [:0]const u8) !ast.Ast {
    var tree = try parser.parse(std.testing.allocator, source);
    errdefer tree.deinit();
    if (tree.hasErrors()) {
        for (tree.diagnostics) |d| {
            std.debug.print("unexpected parse error: {s}\n", .{d.message});
        }
        return error.UnexpectedParseError;
    }
    return tree;
}

fn expectFormatted(source: [:0]const u8, expected_substr: []const u8) !void {
    var tree = try parseOk(source);
    defer tree.deinit();

    var allocating: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer allocating.deinit();
    try ast.formatAst(&tree, &allocating.writer);
    const rendered = allocating.written();
    try std.testing.expect(std.mem.indexOf(u8, rendered, expected_substr) != null);
}

test "1. imports: slash paths, dot paths, member lists, and aliases" {
    var tree = try parseOk(
        \\//// Module level docs
        \\import std/io
        \\import aethel.core.{Option, Result} as core
        \\pub import physics/vec as vec2
    );
    defer tree.deinit();

    try std.testing.expectEqual(@as(usize, 1), tree.module.doc_comments.len);
    try std.testing.expectEqual(@as(usize, 3), tree.module.decls.len);

    const d0 = tree.module.decls[0].kind.import_decl;
    try std.testing.expectEqual(@as(usize, 2), d0.path.len);
    try std.testing.expectEqualStrings("std", d0.path[0].slice(tree.source));
    try std.testing.expectEqualStrings("io", d0.path[1].slice(tree.source));

    const d1 = tree.module.decls[1].kind.import_decl;
    try std.testing.expectEqual(@as(usize, 2), d1.path.len);
    try std.testing.expectEqual(@as(usize, 2), d1.members.len);
    try std.testing.expectEqualStrings("Option", d1.members[0].slice(tree.source));
    try std.testing.expectEqualStrings("core", d1.alias.?.slice(tree.source));

    try std.testing.expect(tree.module.decls[2].is_pub);
    try std.testing.expectEqualStrings("vec2", tree.module.decls[2].kind.import_decl.alias.?.slice(tree.source));
}

test "2. type declarations: ADTs, records, opaque, aliases, arbitrary widths, Int ranges, slices, fn types" {
    var tree = try parseOk(
        \\/// Sum type status
        \\pub type Status {
        \\  Idle
        \\  Moving(speed: u3)
        \\  Poisoned(u4, ticks: i7)
        \\  Dead
        \\}
        \\@layout(aosoa(8))
        \\pub type Entity(t) {
        \\  pub pos: t,
        \\  mut health: Int(0..=100),
        \\  delta: Int(-50..50),
        \\  mask: u24,
        \\  huge: u65535,
        \\  samples: [mut f32],
        \\  cb: fn(i7, u3) -> bool,
        \\  pair: (u8, i16),
        \\}
        \\pub opaque type RustFile
        \\type Meter = f64
    );
    defer tree.deinit();

    try std.testing.expectEqual(@as(usize, 4), tree.module.decls.len);
    const status = tree.module.decls[0].kind.type_decl;
    try std.testing.expectEqual(@as(usize, 1), tree.module.decls[0].doc_comments.len);
    try std.testing.expectEqual(@as(usize, 4), status.body.variants.len);
    try std.testing.expectEqual(@as(usize, 2), status.body.variants[2].fields.len);

    const entity = tree.module.decls[1].kind.type_decl;
    try std.testing.expectEqual(@as(usize, 1), entity.type_params.len);
    try std.testing.expectEqual(@as(usize, 8), entity.body.record.len);
    try std.testing.expect(entity.body.record[1].mutable);
    try std.testing.expect(entity.body.record[1].ty.* == .int_range);
    try std.testing.expect(entity.body.record[1].ty.int_range.inclusive);
    try std.testing.expect(entity.body.record[2].ty.* == .int_range);
    try std.testing.expect(!entity.body.record[2].ty.int_range.inclusive);
    try std.testing.expectEqual(@as(u16, 24), entity.body.record[3].ty.primitive.prim.unsigned);
    try std.testing.expectEqual(@as(u16, 65535), entity.body.record[4].ty.primitive.prim.unsigned);
    try std.testing.expect(entity.body.record[5].ty.* == .slice);
    try std.testing.expect(entity.body.record[5].ty.slice.mutable);
    try std.testing.expect(entity.body.record[6].ty.* == .fn_type);
    try std.testing.expect(entity.body.record[7].ty.* == .tuple);

    const opaque_decl = tree.module.decls[2].kind.type_decl;
    try std.testing.expect(opaque_decl.is_opaque);
    try std.testing.expect(opaque_decl.body == .empty);

    const alias_decl = tree.module.decls[3].kind.type_decl;
    try std.testing.expect(alias_decl.body == .alias);
    try std.testing.expectEqual(ast.TypeExpr{ .primitive = .{
        .span = alias_decl.body.alias.getSpan(),
        .prim = .f64,
    } }, alias_decl.body.alias.*);
}

test "3. path-scoped borrow types (~>.{...} and ~> exclusive .path)" {
    var tree = try parseOk(
        \\fn step(
        \\  entities: Collection(Entity) ~>.{pos, vel},
        \\  single: Entity ~> exclusive .health.current,
        \\  view_param: View(Entity, Exclusive)
        \\) -> _ {
        \\  entities
        \\}
    );
    defer tree.deinit();

    const params = tree.module.decls[0].kind.fn_decl.params;
    try std.testing.expectEqual(@as(usize, 3), params.len);

    const pb0 = params[0].ty.?.path_borrow;
    try std.testing.expect(pb0.borrow.mode == null);
    try std.testing.expectEqual(@as(usize, 2), pb0.borrow.paths.len);
    try std.testing.expectEqualStrings("pos", pb0.borrow.paths[0][0].slice(tree.source));
    try std.testing.expectEqualStrings("vel", pb0.borrow.paths[1][0].slice(tree.source));

    const pb1 = params[1].ty.?.path_borrow;
    try std.testing.expectEqual(ast.BorrowMode.exclusive, pb1.borrow.mode.?);
    try std.testing.expectEqual(@as(usize, 2), pb1.borrow.paths[0].len);
    try std.testing.expectEqualStrings("current", pb1.borrow.paths[0][1].slice(tree.source));

    try std.testing.expect(tree.module.decls[0].kind.fn_decl.ret.?.* == .inferred);
}

test "4. operator precedence, pipelines, saturating/wrapping math, casts, postfix chains" {
    try expectFormatted(
        \\const CHECK: i7 = a + b * c
    , "(+ a (* b c))");

    try expectFormatted(
        \\fn test_ops() {
        \\  let p = a |> f |> g
        \\  let s = hp -| dmg
        \\  let w = x +% y *% z
        \\  let c = x + y as i7
        \\  let q = arr.items[0]?
        \\  q
        \\}
    , "(|> (|> a f) g)");

    try expectFormatted(
        \\fn cast_prec() {
        \\  x + y as i7
        \\}
    , "(+ x (as y i7))");

    try expectFormatted(
        \\fn postfix() {
        \\  arr.items[0]?
        \\}
    , "(? ([] (. arr items) 0))");
}

test "5. Gleam ergonomics: use, lambdas, labeled calls, case arms/guards/ranges/or/alias, todo/panic" {
    var tree = try parseOk(
        \\fn classify(pair: (u8, Status), xs: [u8]) -> u8 {
        \\  use user, _ <- fetch(id: 42, retry: true)
        \\  let handler = fn(e) { e.pos = e.pos +% 1 }
        \\  let _ = case pair.1, user {
        \\    Idle, (0..=10 | 20..=30) as n | Moving(speed: 1..4 as n), _ if n > 2 -> {
        \\      handler(pair.0)
        \\      n
        \\    }
        \\    Poisoned(amt, ..), _ => amt
        \\    Dead, _ -> panic("dead")
        \\    _, _ -> todo("unimplemented")
        \\  }
        \\  case xs {
        \\    [] -> 0
        \\    [head, ..tail] -> head
        \\  }
        \\}
    );
    defer tree.deinit();

    const blk = tree.module.decls[0].kind.fn_decl.body;
    try std.testing.expectEqual(@as(usize, 3), blk.stmts.len);
    try std.testing.expect(blk.stmts[0] == .use_stmt);
    try std.testing.expectEqual(@as(usize, 2), blk.stmts[0].use_stmt.patterns.len);
    try std.testing.expect(blk.stmts[1].let_stmt.value.* == .lambda);
    try std.testing.expect(blk.tail.?.* == .case_expr);

    const case1 = blk.stmts[2].let_stmt.value.case_expr;
    try std.testing.expectEqual(@as(usize, 2), case1.subjects.len);
    try std.testing.expectEqual(@as(usize, 4), case1.arms.len);
    try std.testing.expect(case1.arms[0].guard != null);
    try std.testing.expectEqual(@as(usize, 2), case1.arms[0].alternatives.len);
    try std.testing.expectEqual(@as(usize, 2), case1.arms[0].alternatives[0].len);
    try std.testing.expect(case1.arms[0].alternatives[0][1].alias.inner.* == .or_pat);
    try std.testing.expectEqual(@as(usize, 2), case1.arms[0].alternatives[1].len);
    try std.testing.expect(case1.arms[2].body.* == .panic_expr);
    try std.testing.expect(case1.arms[3].body.* == .todo_expr);

    const case2 = blk.tail.?.case_expr;
    try std.testing.expect(case2.arms[1].alternatives[0][0].* == .list);
    try std.testing.expectEqualStrings("tail", case2.arms[1].alternatives[0][0].list.rest.?.slice(tree.source));
}

test "6. struct-literal disambiguation inside if, while, for, case vs bindings" {
    var tree = try parseOk(
        \\fn disambig(s: Status, items: [Entity], mut x: u8) -> Entity {
        \\  if s == Idle {
        \\    x += 1
        \\  } else if s == Dead {
        \\    return Entity { pos: 0, vel: 1 }
        \\  }
        \\  while x < Limit decreases Limit - x {
        \\    x += 1
        \\  }
        \\  for item in items {
        \\    let p = geom.Vec2 { x: 1, y: 2 }
        \\    item
        \\  }
        \\  Entity { pos: 10, vel }
        \\}
    );
    defer tree.deinit();

    const blk = tree.module.decls[0].kind.fn_decl.body;
    try std.testing.expectEqual(@as(usize, 3), blk.stmts.len);
    try std.testing.expect(blk.stmts[0].expr_stmt.expr.* == .if_expr);
    try std.testing.expect(blk.stmts[1] == .while_stmt);
    try std.testing.expect(blk.stmts[1].while_stmt.decreases != null);
    try std.testing.expect(blk.stmts[2] == .for_stmt);
    const for_let = blk.stmts[2].for_stmt.body.stmts[0].let_stmt.value;
    try std.testing.expect(for_let.* == .record_lit);
    try std.testing.expectEqual(@as(usize, 2), for_let.record_lit.path.len);

    try std.testing.expect(blk.tail.?.* == .record_lit);
    try std.testing.expect(blk.tail.?.record_lit.fields[1].value == null); // shorthand `vel`
}

test "7. layout attributes, view scopes, fork/join parallelism, and decreases" {
    var tree = try parseOk(
        \\pub fn update_motion(entities: Collection(Entity) ~>.{pos, vel}, dt: u16) -> u16 decreases dt {
        \\  @layout(aosoa(8))
        \\  entities |> map_in_place(fn(e) { e.pos = e.pos +% e.vel * dt })
        \\  view exclusive p = entities.pos {
        \\    p[0] = 1
        \\  }
        \\  fork {
        \\    { step_a() }
        \\    { step_b() }
        \\  } join
        \\  dt
        \\}
    );
    defer tree.deinit();

    const f = tree.module.decls[0].kind.fn_decl;
    try std.testing.expect(f.decreases != null);
    try std.testing.expectEqual(@as(usize, 3), f.body.stmts.len);
    try std.testing.expectEqual(@as(usize, 1), f.body.stmts[0].expr_stmt.attrs.len);
    try std.testing.expect(f.body.stmts[0].expr_stmt.attrs[0].payload.layout == .aosoa);
    try std.testing.expect(f.body.stmts[1].expr_stmt.expr.* == .view_expr);
    try std.testing.expectEqual(ast.BorrowMode.exclusive, f.body.stmts[1].expr_stmt.expr.view_expr.mode.?);
    try std.testing.expectEqualStrings("p", f.body.stmts[1].expr_stmt.expr.view_expr.binding.?.slice(tree.source));
    try std.testing.expect(f.body.stmts[2].expr_stmt.expr.* == .fork_expr);
    try std.testing.expect(f.body.stmts[2].expr_stmt.expr.fork_expr.explicit_join);
    try std.testing.expectEqual(@as(usize, 2), f.body.stmts[2].expr_stmt.expr.fork_expr.branches.len);
}

test "8. constitutional laws: preserves, when, always, never, and bare assertions" {
    var tree = try parseOk(
        \\law movement_safe(e: View(Entity, Exclusive), dt: u16) {
        \\  preserves e.health, e.team
        \\  when dt > 0
        \\  always e.health <= 100
        \\  never e.health > 255
        \\}
        \\law status_round_trip(s: Status) {
        \\  Status.decode(Status.encode(s)) == Some(s)
        \\}
    );
    defer tree.deinit();

    try std.testing.expectEqual(@as(usize, 2), tree.module.decls.len);
    const l0 = tree.module.decls[0].kind.law_decl;
    try std.testing.expectEqual(@as(usize, 4), l0.clauses.len);
    try std.testing.expectEqual(@as(usize, 2), l0.clauses[0].preserves.paths.len);
    try std.testing.expect(l0.clauses[1] == .when);
    try std.testing.expect(l0.clauses[2] == .always);
    try std.testing.expect(l0.clauses[3] == .never);

    const l1 = tree.module.decls[1].kind.law_decl;
    try std.testing.expectEqual(@as(usize, 1), l1.clauses.len);
    try std.testing.expect(l1.clauses[0] == .expr);
}

test "9. extern \"rust\" single function and grouped block" {
    var tree = try parseOk(
        \\extern "rust" fn fast_dot(a: [f32], b: [f32]) -> f32
        \\pub extern "rust" {
        \\  pub fn alloc_buf(len: u64) -> RustBuf
        \\  fn free_buf(buf: RustBuf)
        \\}
    );
    defer tree.deinit();

    try std.testing.expectEqual(@as(usize, 2), tree.module.decls.len);
    const e0 = tree.module.decls[0].kind.extern_decl;
    try std.testing.expectEqualStrings("\"rust\"", e0.abi.slice(tree.source));
    try std.testing.expectEqual(@as(usize, 1), e0.fns.len);

    const e1 = tree.module.decls[1].kind.extern_decl;
    try std.testing.expectEqual(@as(usize, 2), e1.fns.len);
    try std.testing.expect(e1.fns[0].is_pub);
    try std.testing.expect(!e1.fns[1].is_pub);
}

test "10. error recovery, combined lexer+parser diagnostics, deep nesting guard, and fuzzing" {
    // Broken first function still recovers cleanly to parse the second valid function.
    const bad_src: [:0]const u8 =
        \\fn broken(x: 123abc {
        \\  let y = 1 +
        \\}
        \\pub fn recovered() -> u7 {
        \\  42_
        \\}
    ;
    var tree = try parser.parse(std.testing.allocator, bad_src);
    defer tree.deinit();
    try std.testing.expect(tree.hasErrors());
    try std.testing.expect(tree.module.decls.len >= 2);
    const last_decl = tree.module.decls[tree.module.decls.len - 1];
    try std.testing.expect(last_decl.kind == .fn_decl);
    try std.testing.expectEqualStrings("recovered", last_decl.kind.fn_decl.name.slice(tree.source));

    // Deep nesting must return structured nesting_depth_exceeded without stack overflow or leak.
    const depth_count = parser.max_nesting_depth + 20;
    const deep_buf = try std.testing.allocator.allocSentinel(u8, "fn f() { ".len + depth_count * 2 + "1 }".len, 0);
    defer std.testing.allocator.free(deep_buf);
    var pos: usize = 0;
    @memcpy(deep_buf[pos..][0.."fn f() { ".len], "fn f() { ");
    pos += "fn f() { ".len;
    for (0..depth_count) |_| {
        deep_buf[pos] = '(';
        pos += 1;
    }
    @memcpy(deep_buf[pos..][0..1], "1");
    pos += 1;
    for (0..depth_count) |_| {
        deep_buf[pos] = ')';
        pos += 1;
    }
    @memcpy(deep_buf[pos..][0.." }".len], " }");
    var deep_tree = try parser.parse(std.testing.allocator, deep_buf);
    defer deep_tree.deinit();
    var saw_depth_err = false;
    for (deep_tree.diagnostics) |d| {
        if (d.kind == .nesting_depth_exceeded) saw_depth_err = true;
    }
    try std.testing.expect(saw_depth_err);
}

test "parser fuzz invariant: arbitrary byte streams terminate without crash or leak" {
    try std.testing.fuzz({}, fuzzParserInvariants, .{});
}

fn fuzzParserInvariants(_: void, smith: *std.testing.Smith) !void {
    const gpa = std.testing.allocator;
    const raw_len: usize = smith.valueRangeAtMost(u16, 0, 512);
    const buf = try gpa.allocSentinel(u8, raw_len, 0);
    defer gpa.free(buf);
    smith.bytes(buf[0..raw_len]);

    var tree = try parser.parse(gpa, buf);
    defer tree.deinit();

    // Verify all diagnostic spans stay within buffer bounds.
    for (tree.diagnostics) |d| {
        try std.testing.expect(d.span.start <= d.span.end);
        try std.testing.expect(d.span.end <= buf.len);
    }

    // Exercise the AST formatter over parsed trees (must succeed cleanly on arbitrary ASTs).
    var allocating: std.Io.Writer.Allocating = .init(gpa);
    defer allocating.deinit();
    try ast.formatAst(&tree, &allocating.writer);
}
