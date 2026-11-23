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
