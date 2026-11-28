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
        \\    left[0] = 42
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
        \\    Particle { cold_id: 1, x: 0.0, vx: 1.0 },
        \\    Particle { cold_id: 2, x: 0.0, vx: 2.0 },
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

    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__aethel_pack: [1]u8") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "if (@sizeOf(PackedTelemetry) > 2)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ".__aethel_set_armed(") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ".__aethel_get_mode()") != null);
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
        \\  Some(v +% 5)
        \\}
        \\fn try_res_step(r: Result(i32, u32)) -> Result(i32, u32) {
        \\  let v = r?
        \\  Ok(v +% 3)
        \\}
        \\fn run_stage_c(fleet: View(Collection(Signal), Exclusive), buf: Collection(i32), dt: f32) -> i32 {
        \\  let f_once = once fn() -> i32 { buf[0] }
        \\  let one = f_once()
        \\  let offset: i32 = 10
        \\  let boosted = apply_twice(identity(1 as i32), fn(n: i32) -> i32 { n +% offset })
        \\  let total = fleet
        \\    |> map_in_place(fn(s) { s.x += s.vx * dt })
        \\    |> map_in_place(fn(s) { s.x += 1.0 })
        \\    |> fold(0.0, fn(acc, s) { acc + s.x })
        \\  let _ = total
        \\  let from_opt = try_opt_step(Some(4)) |> map(fn(x) { x +% 1 }) |> unwrap_or(0)
        \\  let from_res = try_res_step(Some(5 as i32) |> ok_or(1 as u32)) |> map(fn(x) { x +% 2 }) |> unwrap_or(0)
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

test "integer comparisons read through scalar field views and widen their values" {
    const zig_src = try compileToZig(
        \\type Reading { value: u8 }
        \\fn main() -> u8 {
        \\  let mut reading = Reading { value: 17 }
        \\  view exclusive held = reading.value {
        \\    if (300 as u16) > held { 0 } else { 1 }
        \\  }
        \\}
    );
    defer std.testing.allocator.free(zig_src);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "@as(u16, @intCast((held).*))") != null);
}

test "a numeric range snapshots the value read through its bound view" {
    const zig_src = try compileToZig(
        \\type Reading { value: u8, result: u8 }
        \\fn main() -> u8 {
        \\  let mut reading = Reading { value: 2, result: 0 };
        \\  view exclusive count = reading.value {
        \\    for _ in 0..count { reading.result = 19; };
        \\  };
        \\  reading.result
        \\}
    );
    defer std.testing.allocator.free(zig_src);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ": u8 = (count).*;") != null);
}

test "integer assignment and saturated subtraction read scalar views" {
    const zig_src = try compileToZig(
        \\type Reading { value: u8, result: u8 }
        \\fn main() -> u8 {
        \\  let mut reading = Reading { value: 10, result: 0 };
        \\  view exclusive held = reading.value {
        \\    reading.result = held;
        \\    reading.result = held -| 2;
        \\  };
        \\  reading.result
        \\}
    );
    defer std.testing.allocator.free(zig_src);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "reading.result = (held).*;") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "(held).* -| ") != null);
}

test "cross-byte bit-interval codegen emits aethelReadBits/aethelWriteBits and __aethel_pack" {
    const zig_src = try compileToZig(
        \\type CrossPacked {
        \\  a: u12,
        \\  b: u4,
        \\  c: u1,
        \\}
        \\type SignedPacked {
        \\  x: i13,
        \\  y: u5,
        \\  z: i6,
        \\}
        \\fn main() -> u16 {
        \\  let mut p = CrossPacked { a: 1000, b: 9, c: 1 };
        \\  if p.a < 2000 { p.a += 24; };
        \\  p.b = 15;
        \\  let mut sp = SignedPacked { x: -100, y: 17, z: -3 };
        \\  sp.x = -2048;
        \\  (p.a as u16) +% (p.b as u16) +% (sp.y as u16)
        \\}
    );
    defer std.testing.allocator.free(zig_src);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "fn aethelReadBits(") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "fn aethelWriteBits(") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__aethel_pack: [3]u8") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "if (@sizeOf(CrossPacked) > 3)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "if (@sizeOf(SignedPacked) > 3)") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__aethel_set_a(") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "__aethel_get_a()") != null);
}

test "auto-widening, Ring/Field trait dispatch, and Complex(a) codegen" {
    const mod_loader = @import("module_loader.zig");
    const src: [:0]const u8 =
        \\import std/traits.{Semiring, Ring, Field}
        \\import std/complex.{Complex, complex, i_unit, conj, norm_sq}
        \\
        \\fn generate_x(a: u32, b: f64) -> f64 {
        \\  (a as f64) + b
        \\}
        \\fn quad(x: a) -> a with Ring(a) {
        \\  x * x - 2 * x + 1
        \\}
        \\fn main() -> u64 {
        \\  let y: u8 = 200
        \\  let z: u12 = 3000
        \\  let sum32: u32 = y + z
        \\  let _ = generate_x(y, 1.5)
        \\  let q_i32 = quad(5 as i32)
        \\  let c1: Complex(i32) = complex(1 as i32, 2 as i32)
        \\  let c2: Complex(i32) = complex(3 as i32, 4 as i32)
        \\  let c_prod = c1 * c2
        \\  let iu: Complex(i32) = i_unit()
        \\  let i_sq = iu * iu
        \\  let z1: Complex(f64) = complex(1.0, 2.0)
        \\  let z2: Complex(f64) = complex(3.0, 4.0)
        \\  let q_c = quad(z1)
        \\  let _ = q_c
        \\  let _ = (z1 / z2) * z2
        \\  let ok_i = if i_sq == -1 { 1 } else { 0 }
        \\  let ok_prod = if c_prod.re == -5 && c_prod.im == 10 { 1 } else { 0 }
        \\  let ok_q = if q_i32 == 16 { 1 } else { 0 }
        \\  (((2123 as u32) + (10 as Integer(0..=10))) as u64) + (sum32 as u64) + ok_i + ok_prod + ok_q
        \\}
    ;
    const files = [_]mod_loader.MemoryFile{
        .{ .module_key = "main", .path = "main.aethel", .source = src },
    };
    var loaded = try mod_loader.loadFromMemory(std.testing.allocator, "main", &files);
    defer loaded.deinit();
    try std.testing.expect(!loaded.hasErrors());

    var tree = try parser.parse(std.testing.allocator, loaded.combined_source);
    defer tree.deinit();
    if (tree.hasErrors()) {
        for (tree.diagnostics) |d| {
            const s = loaded.combined_source[@min(d.span.start, loaded.combined_source.len)..@min(d.span.end + 30, loaded.combined_source.len)];
            std.debug.print("parse err: {s} near `{s}`\n", .{ d.message, s });
        }
    }
    try std.testing.expect(!tree.hasErrors());

    const mod_infos = try std.testing.allocator.alloc(sema.ModuleSliceInfo, loaded.slices.len);
    defer std.testing.allocator.free(mod_infos);
    for (loaded.slices, 0..) |sl, idx| {
        mod_infos[idx] = .{
            .module_id = sl.module_id,
            .module_key = sl.module_key,
            .start = sl.start,
            .end = sl.end,
        };
    }

    var checked = try sema.analyzeWithModules(std.testing.allocator, &tree, mod_infos, loaded.entry_module_id);
    defer checked.deinit();
    if (checked.hasErrors()) {
        for (checked.diagnostics) |d| {
            const s = loaded.combined_source[@min(d.span.start, loaded.combined_source.len)..@min(d.span.end + 40, loaded.combined_source.len)];
            std.debug.print("complex test sema err: {s} near `{s}`\n", .{ d.message, s });
        }
    }
    try std.testing.expect(!checked.hasErrors());

    var out: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer out.deinit();
    try codegen_zig.emitZig(&tree, &checked, &out.writer);
    const zig_src = out.written();
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "complex_ring") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "complex_field") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ".from_int(@as(i32, -1))") != null);
}

test "exclusive view dereference store, tuple widening, and branch closure codegen" {
    const zig_src = try compileToZig(
        \\type Pair {
        \\  left: u8,
        \\  right: u8,
        \\}
        \\fn apply_pair(args: (fn(u8) -> u8, u8)) -> u8 {
        \\  args.0(args.1)
        \\}
        \\fn main() -> u8 {
        \\  let mut pair = Pair { left: 10, right: 20 };
        \\  view exclusive va = pair.left {
        \\    va = 42;
        \\  };
        \\  let pick = fn(take_first: bool) {
        \\    if take_first { fn(v: u8) { v } } else { fn(v: u8) { 37 } }
        \\  };
        \\  let id = fn(v: u8) { v };
        \\  apply_pair((id, pick(false)(88) +| pair.left)) -| 42
        \\}
    );
    defer std.testing.allocator.free(zig_src);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "(va).* = @as(u8, 42);") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ".@\"0\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, ".@\"1\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, zig_src, "@as(u8, 37)") != null);
}
