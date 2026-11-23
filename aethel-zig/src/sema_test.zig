const std = @import("std");
const parser = @import("parser.zig");
const int_range = @import("int_range.zig");
const layout = @import("layout.zig");
const sema = @import("sema.zig");
const mir = @import("mir.zig");

fn analyzeOk(source: [:0]const u8) !sema.CheckedModule {
    var tree = try parser.parse(std.testing.allocator, source);
    defer tree.deinit();
    if (tree.hasErrors()) {
        for (tree.diagnostics) |d| std.debug.print("parse err: {s}\n", .{d.message});
        return error.UnexpectedParseError;
    }
    var checked = try sema.analyze(std.testing.allocator, &tree);
    errdefer checked.deinit();
    if (checked.hasErrors()) {
        for (checked.diagnostics) |d| std.debug.print("sema err: {s}\n", .{d.message});
        return error.UnexpectedSemaError;
    }
    return checked;
}

fn expectSemaError(source: [:0]const u8, expected_kind: sema.SemaDiagnostic.Kind) !void {
    var tree = try parser.parse(std.testing.allocator, source);
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());
    var checked = try sema.analyze(std.testing.allocator, &tree);
    defer checked.deinit();
    var matched = false;
    for (checked.diagnostics) |d| {
        if (d.kind == expected_kind) matched = true;
    }
    if (!matched) {
        std.debug.print("expected {s}, got {d} diagnostic(s)\n", .{ @tagName(expected_kind), checked.diagnostics.len });
        for (checked.diagnostics) |d| std.debug.print("  actual: {s}: {s}\n", .{ @tagName(d.kind), d.message });
    }
    try std.testing.expect(matched);
}

test "1. arbitrary-width literal checks (i7, u3, u65535)" {
    var ok = try analyzeOk(
        \\fn valid_lits() -> i7 {
        \\  let a: i7 = -64
        \\  let b: i7 = 63
        \\  let c: u3 = 7
        \\  let d = 42_i7
        \\  let e: u65535 = 1_u65535
        \\  a
        \\}
    );
    defer ok.deinit();

    try expectSemaError("fn bad() { let x: i7 = -65 }", .literal_out_of_range);
    try expectSemaError("fn bad() { let x: i7 = 64 }", .literal_out_of_range);
    try expectSemaError("fn bad() { let x: u3 = 8 }", .literal_out_of_range);
    try expectSemaError("fn bad() { let x = 64i7 }", .literal_out_of_range);
}

test "2. automatic minimum bit-width synthesis (IntRange + IntInference)" {
    const r0 = int_range.IntRange{ .bounded = .{ .lo = 0, .hi = 100 } };
    try std.testing.expectEqual(int_range.IntType{ .signed = false, .bits = 7 }, int_range.inferIntegerType(r0).?);

    const r1 = int_range.IntRange{ .bounded = .{ .lo = -50, .hi = 50 } };
    try std.testing.expectEqual(int_range.IntType{ .signed = true, .bits = 7 }, int_range.inferIntegerType(r1).?);

    var checked = try analyzeOk(
        \\type Sensor {
        \\  delta: i7,
        \\  health: Int(0..=100),
        \\}
        \\fn auto_widen(a: i7, b: i7, c: u3, d: u4) -> i8 {
        \\  let sum = a + b
        \\  let prod = c * d
        \\  sum
        \\}
    );
    defer checked.deinit();
    try std.testing.expectEqual(@as(u16, 7), checked.records[0].fields[1].bits);
    try std.testing.expect(!checked.records[0].fields[1].signed);
}

test "3. overflow prevention, branch guard narrowing, saturating & wrapping arithmetic" {
    try expectSemaError(
        \\fn overflow(a: u8, b: u8) -> u8 {
        \\  a + b
        \\}
    , .potential_overflow);

    try expectSemaError(
        \\fn range_overflow(h: Int(0..=100), dmg: u8) -> Int(0..=100) {
        \\  h - dmg
        \\}
    , .potential_overflow);

    var guarded = try analyzeOk(
        \\fn safe_add(a: u8, b: u8, h: Int(0..=100), dmg: u8) -> u8 {
        \\  let clamped: Int(0..=100) = h -| dmg
        \\  let wrapped: u8 = a +% b
        \\  if a <= 100 && b <= 155 {
        \\    a + b
        \\  } else {
        \\    wrapped
        \\  }
        \\}
    );
    defer guarded.deinit();
}

test "4. layout synthesis: FFD packing ([i7, u5, u3, u1]=2B), i24 ABI, and co-borrow conflict separation" {
    var ffd = try analyzeOk(
        \\type PackedBits {
        \\  a: i7,
        \\  b: u5,
        \\  c: u3,
        \\  d: u1,
        \\}
        \\type Media {
        \\  sample: i24,
        \\}
        \\type Entity {
        \\  pos: u32,
        \\  active: u1,
        \\  moving: u1,
        \\}
    );
    defer ffd.deinit();

    try std.testing.expectEqual(@as(usize, 2), ffd.records[0].record_layout.size);
    try std.testing.expectEqual(@as(usize, 1), ffd.records[0].record_layout.alignment);

    try std.testing.expectEqual(@as(usize, 4), ffd.records[1].record_layout.size);
    try std.testing.expectEqual(@as(usize, 4), ffd.records[1].record_layout.alignment);

    try std.testing.expectEqual(@as(usize, 8), ffd.records[2].record_layout.size);
    try std.testing.expectEqual(@as(usize, 4), ffd.records[2].record_layout.alignment);

    // Explicitly verify concurrent exclusive views on two u1 fields insert a CoBorrowGraph conflict
    // and force both fields into separate addressable bytes (`size == 2` instead of `1`).
    var co = try analyzeOk(
        \\type Flags {
        \\  flag_a: u1,
        \\  flag_b: u1,
        \\}
        \\fn touch_both(mut fl: Flags) {
        \\  view exclusive va = fl.flag_a {
        \\    view exclusive vb = fl.flag_b {
        \\      fl.flag_b = 1u1
        \\    }
        \\  }
        \\}
    );
    defer co.deinit();
    try std.testing.expectEqual(@as(usize, 1), co.records[0].conflicts.len);
    try std.testing.expectEqual(@as(usize, 2), co.records[0].record_layout.size);
}

test "5. Benton LNL affine ownership catches use-after-move" {
    try expectSemaError(
        \\opaque type RustHandle
        \\fn close(h: RustHandle) {}
        \\fn bad_use(h: RustHandle) {
        \\  close(h)
        \\  close(h)
        \\}
    , .use_after_move);

    try expectSemaError(
        \\opaque type RustHandle
        \\fn bad_alias(h: RustHandle) {
        \\  let a = move h
        \\  let b = h
        \\}
    , .use_after_move);
}

test "6. path-scoped borrow enforcement (~>.{...}) and active view conflict detection" {
    try expectSemaError(
        \\type Entity {
        \\  pos: u32,
        \\  vel: u32,
        \\  health: u8,
        \\}
        \\fn cheat(e: Entity ~>.{pos, vel}) {
        \\  e.health = 100
        \\}
    , .unauthorized_field_access);

    try expectSemaError(
        \\type Entity {
        \\  health: u8,
        \\}
        \\fn mutate_under_shared(mut e: Entity) {
        \\  view shared s = e.health {
        \\    e.health = 50
        \\  }
        \\}
    , .borrow_conflict);
}

test "7. scoped fork/join race freedom" {
    var disjoint = try analyzeOk(
        \\type Entity {
        \\  pos: u32,
        \\  vel: u32,
        \\}
        \\fn parallel_ok(mut e: Entity) {
        \\  fork {
        \\    { e.pos = 10 }
        \\    { e.vel = 20 }
        \\  } join
        \\}
    );
    defer disjoint.deinit();

    try expectSemaError(
        \\type Entity {
        \\  pos: u32,
        \\}
        \\fn parallel_race(mut e: Entity) {
        \\  fork {
        \\    { e.pos = 10 }
        \\    { e.pos = 20 }
        \\  } join
        \\}
    , .fork_data_race);
}

test "8. Rust FFI boundary rejects sub-byte packed slices and accepts C-ABI slices" {
    var ok = try analyzeOk(
        \\extern "rust" fn fast_sum(xs: [f32], ys: [u32]) -> f32
    );
    defer ok.deinit();

    try expectSemaError(
        \\extern "rust" fn bad_slice(bits: [u3]) -> u32
    , .invalid_ffi_type);

    try expectSemaError(
        \\extern "rust" fn bad_range(x: Int(0..=100)) -> u32
    , .invalid_ffi_type);
}

test "9. constitutional law checks (Tier 0 preserves and interval always/never)" {
    var ok = try analyzeOk(
        \\type Entity {
        \\  pos: u32,
        \\  vel: u32,
        \\  health: Int(0..=100),
        \\}
        \\fn move_pos(entities: Collection(Entity) ~>.{pos, vel}, dt: u32) {
        \\  entities |> map_in_place(fn(e) { e.pos = e.pos +% e.vel *% dt })
        \\}
        \\law movement_safe(e: View(Entity, Exclusive)) {
        \\  preserves e.health
        \\  always e.health <= 100
        \\  never e.health > 200
        \\}
    );
    defer ok.deinit();
    try std.testing.expectEqual(@as(usize, 1), ok.functions[0].preserves.len);
    try std.testing.expectEqual(@as(usize, 2), ok.functions[0].preserves[0]);
    try std.testing.expectEqual(sema.LawVerdict.proved_interval, ok.laws[0].verdict);

    try expectSemaError(
        \\type Entity {
        \\  health: u8,
        \\}
        \\fn hurt(e: Entity ~>.{health}) {
        \\  e.health = 0
        \\}
        \\law no_hurt(e: Entity) {
        \\  preserves e.health
        \\}
    , .law_violation);

    try expectSemaError(
        \\law bad_bound(a: u8) {
        \\  always a <= 100
        \\}
    , .law_violation);
}

test "10. Lean-compatible .mir v1 emission format" {
    var checked = try analyzeOk(
        \\@layout(aosoa(8))
        \\type Player {
        \\  pos: u32,
        \\  delta: i7,
        \\  active: u1,
        \\  health: Int(0..=100),
        \\}
        \\fn step(players: Collection(Player) ~>.{pos, delta}) {
        \\  @layout(aosoa(8))
        \\  players |> map_in_place(fn(p) {
        \\    p.pos = p.pos +% 1u32
        \\  })
        \\}
        \\law keep_health(p: View(Player, Exclusive)) {
        \\  preserves p.health, p.active
        \\}
    );
    defer checked.deinit();

    var out: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer out.deinit();
    try mir.emitMir(&checked, &out.writer);
    const mir_txt = out.written();

    try std.testing.expect(std.mem.indexOf(u8, mir_txt, "mir_version 1\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, mir_txt, "record Player 8\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, mir_txt, "  field u32\n  field i7\n  field u1\n  field u7\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, mir_txt, "collection Player aosoa 8 4\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, mir_txt, "  effect_write 0\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, mir_txt, "  preserves 3\n") != null);
}
