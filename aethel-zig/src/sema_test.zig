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

test "11. two-phase lazy exclusive borrow allows shared reads until activation write" {
    var ok = try analyzeOk(
        \\type Spaceship {
        \\  x: i32,
        \\  y: i32,
        \\}
        \\fn two_phase(mut ship: Spaceship) -> i32 {
        \\  view exclusive w = ship {
        \\    let snap = ship.x
        \\    w.x = snap +% 10
        \\  }
        \\  ship.x
        \\}
    );
    defer ok.deinit();

    // Activating a reserved exclusive view while a shared view is still live must fail.
    try expectSemaError(
        \\type Spaceship { x: i32 }
        \\fn blocked_activate(mut ship: Spaceship) -> i32 {
        \\  let mut out: i32 = 0
        \\  view shared r = ship.x {
        \\    view exclusive w = ship.x {
        \\      w.x = 10
        \\    }
        \\    let _ = r
        \\  }
        \\  out
        \\}
    , .borrow_conflict);

    // Raw read after activation while `w` still has a later use must fail.
    try expectSemaError(
        \\type Spaceship { x: i32, y: i32 }
        \\fn raw_read_after_activate(mut ship: Spaceship) -> i32 {
        \\  view exclusive w = ship {
        \\    w.x = 10
        \\    let clash = ship.x
        \\    w.y = clash
        \\  }
        \\  ship.x
        \\}
    , .borrow_conflict);
}

test "12. automatic last-use early view release unlocks same-block mutation and reads" {
    var ok = try analyzeOk(
        \\type Spaceship {
        \\  x: i32,
        \\  y: i32,
        \\}
        \\fn early_release_demo(mut ship: Spaceship) -> i32 {
        \\  view shared r = ship {
        \\    let snap = r.x
        \\    ship.x = snap +% 5
        \\  }
        \\  view exclusive w = ship {
        \\    w.x = ship.x +% 3
        \\    let after = ship.x
        \\    let _ = after
        \\  }
        \\  ship.x
        \\}
    );
    defer ok.deinit();

    // Mutating `ship.x` BEFORE the last use of `r` must still be rejected.
    try expectSemaError(
        \\type Spaceship { x: i32 }
        \\fn early_conflict(mut ship: Spaceship) -> i32 {
        \\  view shared r = ship {
        \\    ship.x = 5
        \\    let snap = r.x
        \\    let _ = snap
        \\  }
        \\  ship.x
        \\}
    , .borrow_conflict);
}

test "13. affine index and half-open slice disjointness (AffineIndex.lean)" {
    var ok = try analyzeOk(
        \\fn parallel_indexed(mut arr: [mut u32], i: u32, j: u32, mid: u32) {
        \\  if i != j {
        \\    fork {
        \\      { arr[i] = 1u32 }
        \\      { arr[j] = 2u32 }
        \\    } join
        \\  }
        \\  fork {
        \\    { arr[0] = 3u32 }
        \\    { arr[1] = 4u32 }
        \\  } join
        \\  fork {
        \\    { arr[i] = 5u32 }
        \\    { arr[i + 1] = 6u32 }
        \\  } join
        \\  view exclusive left = arr[0..mid] {
        \\    view exclusive right = arr[mid..arr.len] {
        \\      fork {
        \\        { left[0] = 10u32 }
        \\        { right[0] = 20u32 }
        \\      } join
        \\    }
        \\  }
        \\}
    );
    defer ok.deinit();

    // Unguarded `arr[i]` and `arr[j]` must fail with fork_data_race.
    try expectSemaError(
        \\fn bad_unguarded(mut arr: [mut u32], i: u32, j: u32) {
        \\  fork {
        \\    { arr[i] = 1u32 }
        \\    { arr[j] = 2u32 }
        \\  } join
        \\}
    , .fork_data_race);

    // Reassigning `i` invalidates the SSA guard fact `i != j`.
    try expectSemaError(
        \\fn bad_reassigned(mut arr: [mut u32], mut i: u32, j: u32) {
        \\  if i != j {
        \\    i = i +% 1u32
        \\    fork {
        \\      { arr[i] = 1u32 }
        \\      { arr[j] = 2u32 }
        \\    } join
        \\  }
        \\}
    , .fork_data_race);

    // Overlapping slices `[0..mid)` and `[0..n)` conflict under exclusive view.
    try expectSemaError(
        \\fn bad_overlap_slices(mut arr: [mut u32], mid: u32, n: u32) {
        \\  view exclusive left = arr[0..mid] {
        \\    view exclusive right = arr[0..n] {
        \\      let _ = left
        \\      let _ = right
        \\    }
        \\  }
        \\}
    , .borrow_conflict);
}

test "14. transitive call-graph effects and returned caller-rooted Views" {
    // 1. Transitive law violation through helper declared AFTER caller
    try expectSemaError(
        \\type Spaceship { x: i32, shield_on: u1 }
        \\fn outer(s: Spaceship ~>.{x, shield_on}) {
        \\  helper_hurt(s)
        \\}
        \\fn helper_hurt(s: Spaceship ~>.{shield_on}) {
        \\  s.shield_on = 0u1
        \\}
        \\law keep_shield(s: View(Spaceship, Exclusive)) {
        \\  preserves s.shield_on
        \\}
    , .law_violation);

    // 2. Transitive fork_data_race through helper call
    try expectSemaError(
        \\type Spaceship { x: i32, y: i32 }
        \\fn bump_x(s: Spaceship ~>.{x}) {
        \\  s.x = s.x +% 1
        \\}
        \\fn race_via_call(mut s: Spaceship) {
        \\  fork {
        \\    { bump_x(s) }
        \\    { s.x = 9 }
        \\  } join
        \\}
    , .fork_data_race);

    // 3. Transitive unauthorized field mutation via ~>.{x}
    try expectSemaError(
        \\type Spaceship { x: i32, y: i32 }
        \\fn constrained(s: Spaceship ~>.{x}) {
        \\  touch_y(s)
        \\}
        \\fn touch_y(s: Spaceship ~>.{y}) {
        \\  s.y = 5
        \\}
    , .unauthorized_field_access);

    // 4. Positive returned caller-rooted View
    var ok_ret = try analyzeOk(
        \\type Spaceship { x: i32, y: i32 }
        \\fn borrow_ship(s: Spaceship ~>.{x}) -> View(Spaceship, Exclusive) {
        \\  s
        \\}
        \\fn use_returned(mut s: Spaceship) -> i32 {
        \\  let v = borrow_ship(s)
        \\  v.x = 77
        \\  s.x
        \\}
    );
    defer ok_ret.deinit();

    // 5. Returning a View to a stack-local variable must fail
    try expectSemaError(
        \\type Spaceship { x: i32, y: i32 }
        \\fn dangling_local() -> View(Spaceship, Exclusive) {
        \\  let mut s = Spaceship { x: 1, y: 2 }
        \\  s
        \\}
    , .borrow_conflict);
}

test "15. Stage A .mir v1 emission includes two-phase perm_* and disjoint_* certificates" {
    var checked = try analyzeOk(
        \\type Ship { x: i32, y: i32 }
        \\fn stage_a_fn(mut s: Ship, mut arr: [mut u32], i: u32, j: u32, mid: u32) {
        \\  view exclusive w = s {
        \\    let snap = s.x
        \\    w.x = snap +% 1
        \\  }
        \\  if i != j {
        \\    fork {
        \\      { arr[i] = 1u32 }
        \\      { arr[j] = 2u32 }
        \\    } join
        \\  }
        \\  view exclusive l = arr[0..mid] {
        \\    view exclusive r = arr[mid..arr.len] {
        \\      fork {
        \\        { l[0] = 3u32 }
        \\        { r[0] = 4u32 }
        \\      } join
        \\    }
        \\  }
        \\}
    );
    defer checked.deinit();

    var out: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer out.deinit();
    try mir.emitMir(&checked, &out.writer);
    const mir_txt = out.written();

    try std.testing.expect(std.mem.indexOf(u8, mir_txt, "perm_alloc ") != null);
    try std.testing.expect(std.mem.indexOf(u8, mir_txt, "reserved\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, mir_txt, "perm_activate ") != null);
    try std.testing.expect(std.mem.indexOf(u8, mir_txt, "perm_release ") != null);
    try std.testing.expect(std.mem.indexOf(u8, mir_txt, "disjoint_idx ") != null);
    try std.testing.expect(std.mem.indexOf(u8, mir_txt, "disjoint_slice ") != null);
}

test "16. Stage B @layout(auto), hot-first ordering, and @parallel scalar/field race checks" {
    // 1. @layout(auto) picks AoSoA(8) on SIMD hot-field traversal and reorders hot fields before cold ones
    var auto_res = try analyzeOk(
        \\@layout(auto)
        \\type Particle {
        \\  note_tag: u32,
        \\  cooldown: f32,
        \\  x: f32,
        \\  vx: f32,
        \\}
        \\fn step_all(fleet: Collection(Particle), dt: f32) {
        \\  fleet |> map_in_place(fn(p) {
        \\    p.x += p.vx * dt
        \\  })
        \\}
    );
    defer auto_res.deinit();

    try std.testing.expectEqual(@as(usize, 1), auto_res.records.len);
    const p_rec = auto_res.records[0];
    try std.testing.expect(p_rec.collection_layout != null);
    try std.testing.expect(p_rec.collection_layout.? == .aosoa);
    try std.testing.expectEqual(@as(usize, 8), p_rec.collection_layout.?.aosoa);
    try std.testing.expect(p_rec.auto_layout_decision != null);
    // Hot fields (x=2, vx=3) must have lower byte_offset than cold fields (note_tag=0, cooldown=1)
    try std.testing.expect(!p_rec.hot_fields[0]);
    try std.testing.expect(!p_rec.hot_fields[1]);
    try std.testing.expect(p_rec.hot_fields[2]);
    try std.testing.expect(p_rec.hot_fields[3]);
    try std.testing.expect(p_rec.record_layout.fields[2].byte_offset < p_rec.record_layout.fields[0].byte_offset);
    try std.testing.expect(p_rec.record_layout.fields[3].byte_offset < p_rec.record_layout.fields[1].byte_offset);

    // 2. @layout(auto) picks AoS on tiny len<=2 non-SIMD collections
    var tiny_res = try analyzeOk(
        \\@layout(auto)
        \\type TinyRec {
        \\  a: u32,
        \\  b: u32,
        \\}
        \\fn mk() -> u32 {
        \\  let mut items: Collection(TinyRec) = [
        \\    TinyRec { a: 1u32, b: 2u32 },
        \\    TinyRec { a: 3u32, b: 4u32 },
        \\  ]
        \\  items[0].a
        \\}
    );
    defer tiny_res.deinit();
    try std.testing.expect(tiny_res.records[0].collection_layout.? == .aos);

    // 3. @parallel fork accepts disjoint branches + identically named branch-local accumulators + read-read shared scalar
    var ok_par = try analyzeOk(
        \\type Pair {
        \\  left: u32,
        \\  right: u32,
        \\}
        \\fn ok_parallel(mut pair: Pair, scale: u32) {
        \\  @parallel fork {
        \\    {
        \\      let mut acc: u32 = 1u32
        \\      acc = acc +% scale
        \\      pair.left = acc
        \\    }
        \\    {
        \\      let mut acc: u32 = 2u32
        \\      acc = acc +% scale
        \\      pair.right = acc
        \\    }
        \\  } join
        \\}
    );
    defer ok_par.deinit();

    // 4. @parallel fork rejects outer scalar variable write/read and write/write races
    try expectSemaError(
        \\fn bad_scalar_rw(mut total: u32) -> u32 {
        \\  @parallel fork {
        \\    { total = total +% 1u32 }
        \\    { let _ = total }
        \\  } join
        \\  total
        \\}
    , .fork_data_race);

    try expectSemaError(
        \\fn bad_scalar_ww() -> u32 {
        \\  let mut total: u32 = 0u32
        \\  @parallel fork {
        \\    { total = 1u32 }
        \\    { total = 2u32 }
        \\  } join
        \\  total
        \\}
    , .fork_data_race);
}

test "17. Stage C LNL once closures, rank-1 generics, fused pipelines, combinators, and ? propagation" {
    // 1. once fn captures affine Collection and can be called once; double call or post-capture use fails.
    var ok_once = try analyzeOk(
        \\fn consume_with_once(buf: Collection(u32)) -> u32 {
        \\  let f: once fn() -> u32 = once fn() -> u32 { buf[0] }
        \\  f()
        \\}
    );
    defer ok_once.deinit();

    try expectSemaError(
        \\fn double_once_call(buf: Collection(u32)) -> u32 {
        \\  let f = once fn() -> u32 { buf[0] }
        \\  let a = f()
        \\  let b = f()
        \\  a +% b
        \\}
    , .use_after_move);

    try expectSemaError(
        \\fn use_after_once_capture(buf: Collection(u32)) -> u32 {
        \\  let f = once fn() -> u32 { buf[0] }
        \\  let x = buf[0]
        \\  x +% f()
        \\}
    , .use_after_move);

    try expectSemaError(
        \\fn reusable_captures_affine(buf: Collection(u32)) -> fn() -> u32 {
        \\  fn() -> u32 { buf[0] }
        \\}
    , .affine_capture);

    try expectSemaError(
        \\fn reusable_captures_once(buf: Collection(u32)) -> fn() -> u32 {
        \\  let f = once fn() -> u32 { buf[0] }
        \\  fn() -> u32 { f() }
        \\}
    , .affine_capture);

    // 2. Gleam-style rank-1 generics
    var ok_gen = try analyzeOk(
        \\fn identity(x: a) -> a { x }
        \\fn apply_twice(x: a, f: fn(a) -> a) -> a { f(f(x)) }
        \\fn use_gen() -> i32 {
        \\  let b: bool = identity(true)
        \\  let _ = b
        \\  apply_twice(10i32, fn(n: i32) -> i32 { n +% 1i32 })
        \\}
    );
    defer ok_gen.deinit();

    try expectSemaError(
        \\fn same_pair(x: a, y: a) -> a { x }
        \\fn bad_unify() -> i32 {
        \\  same_pair(1i32, true)
        \\}
    , .type_mismatch);

    // 3. Chained map_in_place |> map_in_place |> fold pipeline + hot-field marking
    var ok_pipe = try analyzeOk(
        \\@layout(auto)
        \\type Signal {
        \\  cold_tag: u32,
        \\  x: f32,
        \\  vx: f32,
        \\}
        \\fn fuse_sum(fleet: View(Collection(Signal), Exclusive), dt: f32) -> f32 {
        \\  fleet
        \\    |> map_in_place(fn(s) { s.x += s.vx * dt })
        \\    |> map_in_place(fn(s) { s.x += 1.0f32 })
        \\    |> fold(0.0f32, fn(acc, s) { acc + s.x })
        \\}
    );
    defer ok_pipe.deinit();
    try std.testing.expect(!ok_pipe.records[0].hot_fields[0]);
    try std.testing.expect(ok_pipe.records[0].hot_fields[1]);
    try std.testing.expect(ok_pipe.records[0].hot_fields[2]);
    try std.testing.expect(ok_pipe.records[0].collection_layout.? == .aosoa);

    // 4. Option/Result combinators + ? early-return propagation checks
    var ok_comb = try analyzeOk(
        \\fn comb_opt(x: Option(i32)) -> i32 {
        \\  x |> map(fn(v) { v *% 2i32 }) |> and_then(fn(v) { Some(v +% 1i32) }) |> unwrap_or(0i32)
        \\}
        \\fn comb_res(x: Option(i32)) -> i32 {
        \\  x |> ok_or(404u32) |> map(fn(v) { v +% 10i32 }) |> unwrap_or(-1i32)
        \\}
        \\fn prop_opt(a: Option(i32)) -> Option(i32) {
        \\  let v = a?
        \\  Some(v +% 1i32)
        \\}
        \\fn prop_res(r: Result(i32, u32)) -> Result(i32, u32) {
        \\  let v = r?
        \\  Ok(v +% 2i32)
        \\}
    );
    defer ok_comb.deinit();

    try expectSemaError(
        \\fn bad_try(a: Option(i32)) -> i32 {
        \\  a?
        \\}
    , .type_mismatch);
}
