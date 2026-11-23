const std = @import("std");
const parser = @import("parser.zig");
const sema = @import("sema.zig");
const codegen_zig = @import("codegen_zig.zig");

fn compileToZig(source: [:0]const u8) ![]u8 {
    var tree = try parser.parse(std.testing.allocator, source);
    defer tree.deinit();
    if (tree.hasErrors()) {
        for (tree.diagnostics) |d| std.debug.print("parse err: {s}\n", .{d.message});
        return error.UnexpectedParseError;
    }
    var checked = try sema.analyze(std.testing.allocator, &tree);
    defer checked.deinit();
    if (checked.hasErrors()) {
        for (checked.diagnostics) |d| std.debug.print("sema err: {s}\n", .{d.message});
        return error.UnexpectedSemaError;
    }
    var out: std.Io.Writer.Allocating = .init(std.testing.allocator);
    errdefer out.deinit();
    try codegen_zig.emitZig(&tree, &checked, &out.writer);
    return try out.toOwnedSlice();
}

test "1. codegen: hello world produces Zig 0.17 entrypoint and aethelPrint" {
    const zig_src = try compileToZig(
        \\fn main() {
        \\  println("Hello, world!")
        \\}
    );
    defer std.testing.allocator.free(zig_src);

    try std.testing.expect(std.mem.indexOf(u8, zig_src, "pub fn main(init: std.process.Init) void") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "aethelPrint(.{ \"Hello, world!\" }, true, false)") != null);
}

test "2. codegen: arbitrary-width i7/u3/u7 math, signed division, and guarded widening" {
    const zig_src = try compileToZig(
        \\fn widen_math(a: i7, b: i7, c: u3, d: u4) -> i8 {
        \\  let prod: u7 = c * d
        \\  let q: i8 = (a + b) / 2
        \\  let _ = prod
        \\  q
        \\}
        \\fn guarded(a: u8, b: u8) -> u8 {
        \\  if a <= 100 && b <= 155 {
        \\    a + b
        \\  } else {
        \\    255
        \\  }
        \\}
    );
    defer std.testing.allocator.free(zig_src);

    try std.testing.expect(std.mem.indexOf(u8, zig_src, "fn widen_math(a: i7, b: i7, c: u3, d: u4) i8") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "const prod: u7 = (@as(u7, @intCast(c)) * @as(u7, @intCast(d)))") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "@divTrunc(") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "(a <= @as(u8, 100)) and (b <= @as(u8, 155))") != null);
}

test "3. codegen: saturating Int(0..=100) lowers to aethelClamp" {
    const zig_src = try compileToZig(
        \\fn damage(h: Int(0..=100), dmg: u8) -> Int(0..=100) {
        \\  h -| dmg
        \\}
    );
    defer std.testing.allocator.free(zig_src);

    try std.testing.expect(std.mem.indexOf(u8, zig_src, "fn damage(h: u7, dmg: u8) u7") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "aethelClamp(u7, (@as(i128, h) - @as(i128, dmg)), 0, 100)") != null);
}

test "4. codegen: records, path-borrow pointer lowering, ADTs, case, and erased laws" {
    const zig_src = try compileToZig(
        \\type Player {
        \\  pos: i32,
        \\  delta: i7,
        \\  health: Int(0..=100),
        \\}
        \\type Status {
        \\  Idle,
        \\  Moving(u8),
        \\}
        \\fn step(p: Player ~>.{pos, delta}) {
        \\  p.pos = p.pos +% (p.delta as i32)
        \\}
        \\fn speed_of(s: Status) -> u8 {
        \\  case s {
        \\    Idle -> 0
        \\    Moving(spd) -> spd
        \\  }
        \\}
        \\law keep_hp(p: View(Player, Exclusive)) {
        \\  preserves p.health
        \\}
        \\fn run_demo() -> u8 {
        \\  let mut pl = Player { pos: 10, delta: -2, health: 100 }
        \\  step(pl)
        \\  speed_of(Moving(12))
        \\}
    );
    defer std.testing.allocator.free(zig_src);

    try std.testing.expect(std.mem.indexOf(u8, zig_src, "const Player = struct {") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "const Status = union(enum) {") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "fn step(p: *Player) void") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "step(&pl);") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "switch (s) {") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "// law keep_hp: erased (proved_tier0)") != null);
}

test "5. codegen: extern rust C-ABI, inclusive/exclusive for loops, and string concat" {
    const zig_src = try compileToZig(
        \\extern "rust" fn fast_dot(xs: [f32], n: u32) -> f32
        \\fn greet(name: String) -> String {
        \\  let mut sum: u8 = 0
        \\  for i in 0..=4 {
        \\    sum = sum +% i
        \\  }
        \\  let _ = sum
        \\  "hi " <> name
        \\}
    );
    defer std.testing.allocator.free(zig_src);

    try std.testing.expect(std.mem.indexOf(u8, zig_src, "extern \"c\" fn fast_dot(xs_ptr: [*]const f32, xs_len: usize, n: u32) f32;") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "if (__i_1 <= __end_1)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "aethelConcat(\"hi \", name)") != null);
}

test "6. codegen: half-open slices, runtime index casts, and returned Views" {
    const zig_src = try compileToZig(
        \\type Spaceship { x: i32, y: i32 }
        \\fn borrow_ship(s: Spaceship ~>.{x}) -> View(Spaceship, Exclusive) {
        \\  s
        \\}
        \\fn slice_and_view(mut arr: [mut u32], mid: u32, mut ship: Spaceship) -> u32 {
        \\  view exclusive left = arr[0..mid] {
        \\    left[0] = 42u32
        \\  }
        \\  let v = borrow_ship(ship)
        \\  v.x = 10
        \\  arr[0]
        \\}
    );
    defer std.testing.allocator.free(zig_src);

    try std.testing.expect(std.mem.indexOf(u8, zig_src, "fn borrow_ship(s: *Spaceship) *Spaceship") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "arr[0..@as(usize, @intCast(mid))]") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "const v: *Spaceship = borrow_ship(&ship);") != null);
}

test "7. codegen: FFD packed bins, CompactADT, @layout(auto) SIMD AoSoA, and @parallel std.Thread" {
    const zig_src = try compileToZig(
        \\type PackedTelemetry {
        \\  ok: bool,
        \\  mode: Int(0..=7),
        \\  armed: bool,
        \\  code: u8,
        \\}
        \\type CompactStatus {
        \\  Idle,
        \\  Moving(u4),
        \\  Poisoned(u4),
        \\  Dead,
        \\}
        \\@layout(auto)
        \\type Particle {
        \\  cold_id: u32,
        \\  x: f32,
        \\  vx: f32,
        \\}
        \\fn read_status(s: CompactStatus) -> u8 {
        \\  case s {
        \\    Idle -> 0
        \\    Moving(spd) -> spd as u8
        \\    Poisoned(dmg) -> dmg as u8
        \\    Dead -> 99
        \\  }
        \\}
        \\fn run_stage_b(dt: f32) -> u8 {
        \\  let mut tel = PackedTelemetry { ok: true, mode: 3, armed: false, code: 7 }
        \\  tel.armed = true
        \\  tel.mode = 5
        \\  let mut swarm: Collection(Particle) = [
        \\    Particle { cold_id: 1u32, x: 0.0f32, vx: 1.0f32 },
        \\    Particle { cold_id: 2u32, x: 0.0f32, vx: 2.0f32 },
        \\  ]
        \\  swarm |> map_in_place(fn(p) {
        \\    p.x += p.vx * dt
        \\  })
        \\  let mut sum_a: u8 = 0
        \\  let mut sum_b: u8 = 0
        \\  @parallel fork {
        \\    { sum_b = tel.code +% (tel.mode as u8) }
        \\    { sum_a = read_status(Moving(4)) +% tel.code }
        \\  } join
        \\  sum_a +% sum_b
        \\}
    );
    defer std.testing.allocator.free(zig_src);

    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__bin_1: packed struct(u8)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "if (@sizeOf(PackedTelemetry) > 2)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ".__bin_1.") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "const CompactStatus = packed struct(u8)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "pub const Tag = enum(u2)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "if (@sizeOf(CompactStatus) != 1)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ".tag) {") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "align(64)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "@Vector(8, f32)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "@splat(dt)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "std.Thread.spawn(") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ".join();") != null);
}

test "8. codegen: LNL once closures, generics, fused SIMD+fold pipelines, combinator fusion, and ?" {
    const zig_src = try compileToZig(
        \\@layout(auto)
        \\type Signal {
        \\  tag: u32,
        \\  x: f32,
        \\  vx: f32,
        \\}
        \\fn identity(x: a) -> a { x }
        \\fn apply_twice(x: a, f: fn(a) -> a) -> a {
        \\  f(f(x))
        \\}
        \\fn try_opt_step(o: Option(i32)) -> Option(i32) {
        \\  let v = o?
        \\  Some(v +% 5i32)
        \\}
        \\fn try_res_step(r: Result(i32, u32)) -> Result(i32, u32) {
        \\  let v = r?
        \\  Ok(v +% 3i32)
        \\}
        \\fn run_stage_c(fleet: View(Collection(Signal), Exclusive), buf: Collection(i32), dt: f32) -> i32 {
        \\  let f_once = once fn() -> i32 { buf[0] }
        \\  let one = f_once()
        \\  let offset: i32 = 10i32
        \\  let boosted = apply_twice(identity(1i32), fn(n: i32) -> i32 { n +% offset })
        \\  let total = fleet
        \\    |> map_in_place(fn(s) { s.x += s.vx * dt })
        \\    |> map_in_place(fn(s) { s.x += 1.0f32 })
        \\    |> fold(0.0f32, fn(acc, s) { acc + s.x })
        \\  let _ = total
        \\  let from_opt = try_opt_step(Some(4i32)) |> map(fn(x) { x +% 1i32 }) |> unwrap_or(0i32)
        \\  let from_res = try_res_step(Some(5i32) |> ok_or(1u32)) |> map(fn(x) { x +% 2i32 }) |> unwrap_or(0i32)
        \\  one +% boosted +% from_opt +% from_res
        \\}
    );
    defer std.testing.allocator.free(zig_src);

    try std.testing.expect(std.mem.indexOf(u8, zig_src, "fn AethelResult(comptime T: type, comptime E: type) type") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "fn aethelCall(f: anytype, args: anytype)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "fn identity(comptime __T_a: type, x: __T_a) __T_a") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "fn apply_twice(comptime __T_a: type, x: __T_a, f: anytype) __T_a") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "aethelCall(") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "orelse return null") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "return .{ .Err = __err_") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "// Categorical fusion: 2 map_in_place stage(s) + fold deforestation fused into 1 pass") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "@Vector(8, f32)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "// Categorical fusion: Option.map |> unwrap_or") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "// Categorical fusion: Result.map |> unwrap_or") != null);
}
