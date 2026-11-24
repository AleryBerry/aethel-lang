const std = @import("std");
const Io = std.Io;
const ast = @import("ast.zig");
const parser = @import("parser.zig");
const sema = @import("sema.zig");
const mir = @import("mir.zig");
const rust_ffi = @import("rust_ffi.zig");
const codegen_zig = @import("codegen_zig.zig");

fn expectSemaError(source: [:0]const u8, expected: sema.SemaDiagnostic.Kind) !void {
    var tree = try parser.parse(std.testing.allocator, source);
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());

    var checked = try sema.analyze(std.testing.allocator, &tree);
    defer checked.deinit();
    for (checked.diagnostics) |d| {
        if (d.kind == expected) return;
    }
    std.debug.print("expected sema diagnostic {s}, got {d} diagnostic(s)\n", .{
        @tagName(expected),
        checked.diagnostics.len,
    });
    return error.ExpectedSemaErrorMissing;
}

fn checkAndEmitAll(source: [:0]const u8) !struct {
    checked: sema.CheckedModule,
    tree: ast.Ast,
    mir_txt: []u8,
    zig_txt: []u8,
    rust_txt: []u8,
} {
    var tree = try parser.parse(std.testing.allocator, source);
    errdefer tree.deinit();
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
    var mir_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    try mir.emitMir(&checked, &mir_buf.writer);
    var zig_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    try codegen_zig.emitZig(&tree, &checked, &zig_buf.writer);
    var rust_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    try rust_ffi.emitRustAdapter(&tree, &checked, null, &rust_buf.writer);
    return .{
        .checked = checked,
        .tree = tree,
        .mir_txt = try mir_buf.toOwnedSlice(),
        .zig_txt = try zig_buf.toOwnedSlice(),
        .rust_txt = try rust_buf.toOwnedSlice(),
    };
}

test "1. Stage F: Semigroup + Monoid default vs named instance using, plus trait_law MIR" {
    const src: [:0]const u8 =
        \\pub trait Semigroup(a) {
        \\  fn combine(x: a, y: a) -> a
        \\  law assoc(x: a, y: a, z: a) {
        \\    always combine(combine(x, y), z) == combine(x, combine(y, z))
        \\  }
        \\}
        \\pub trait Monoid(a) <= Semigroup(a) {
        \\  fn empty() -> a
        \\  law left_id(x: a) { always combine(empty(), x) == x }
        \\  law right_id(x: a) { always combine(x, empty()) == x }
        \\}
        \\pub default instance sum_u32: Monoid(u32) {
        \\  fn empty() -> u32 { 0u32 }
        \\  fn combine(x: u32, y: u32) -> u32 { x +| y }
        \\}
        \\pub instance max_u32: Monoid(u32) {
        \\  fn empty() -> u32 { 0u32 }
        \\  fn combine(x: u32, y: u32) -> u32 { max(x, y) }
        \\}
        \\pub fn fold_slice(xs: [a]) -> a with Monoid(a) {
        \\  let mut acc: a = empty()
        \\  for x in xs {
        \\    acc = combine(acc, x)
        \\  }
        \\  acc
        \\}
        \\pub fn main() -> u32 {
        \\  let scores = [3u32, 9u32, 4u32]
        \\  let total = fold_slice(scores)
        \\  let peak = fold_slice(scores) using max_u32
        \\  total +| peak
        \\}
    ;
    var res = try checkAndEmitAll(src);
    defer {
        res.checked.deinit();
        res.tree.deinit();
        std.testing.allocator.free(res.mir_txt);
        std.testing.allocator.free(res.zig_txt);
        std.testing.allocator.free(res.rust_txt);
    }

    try std.testing.expectEqual(@as(usize, 2), res.checked.traits.len);
    try std.testing.expectEqual(@as(usize, 2), res.checked.instances.len);
    try std.testing.expect(std.mem.indexOf(u8, res.mir_txt, "trait_law sum_u32.") != null);
    try std.testing.expect(std.mem.indexOf(u8, res.mir_txt, "trait_law max_u32.") != null);
    try std.testing.expect(std.mem.indexOf(u8, res.zig_txt, "__Inst_sum_u32") != null);
    try std.testing.expect(std.mem.indexOf(u8, res.zig_txt, "__Inst_max_u32") != null);
}

test "2. Stage F: Monad(Option) <= Applicative(Option) <= Functor(Option) with auto fmap/ap & laws" {
    const src: [:0]const u8 =
        \\pub trait Functor(f(_)) {
        \\  fn fmap(fa: f(a), g: fn(a) -> b) -> f(b)
        \\}
        \\pub trait Applicative(f(_)) <= Functor(f) {
        \\  fn pure(x: a) -> f(a)
        \\  fn ap(ff: f(fn(a) -> b), fa: f(a)) -> f(b)
        \\}
        \\pub trait Monad(f(_)) <= Applicative(f) {
        \\  fn bind(ma: f(a), k: fn(a) -> f(b)) -> f(b)
        \\  law left_id(x: a, k: fn(a) -> f(b)) { always bind(pure(x), k) == k(x) }
        \\  law right_id(m: f(a)) { always bind(m, fn(x: a) -> f(a) { pure(x) }) == m }
        \\}
        \\pub default instance opt_monad: Monad(Option) {
        \\  fn pure(x: a) -> Option(a) { Some(x) }
        \\  fn bind(ma: Option(a), k: fn(a) -> Option(b)) -> Option(b) {
        \\    case ma {
        \\      None -> None
        \\      Some(v) -> k(v)
        \\    }
        \\  }
        \\}
        \\pub fn inc_opt(x: f(u32)) -> f(u32) with Functor(f) {
        \\  fmap(x, fn(n: u32) -> u32 { n +% 1u32 })
        \\}
        \\pub fn main() -> u32 {
        \\  let mapped = inc_opt(Some(41u32))
        \\  mapped |> unwrap_or(0u32)
        \\}
    ;
    var res = try checkAndEmitAll(src);
    defer {
        res.checked.deinit();
        res.tree.deinit();
        std.testing.allocator.free(res.mir_txt);
        std.testing.allocator.free(res.zig_txt);
        std.testing.allocator.free(res.rust_txt);
    }
    try std.testing.expect(std.mem.indexOf(u8, res.zig_txt, "__Inst_opt_monad") != null);
    try std.testing.expect(std.mem.indexOf(u8, res.zig_txt, "pub fn fmap(") != null);
}

test "3. Stage F: unlawful Monoid and ambiguous default instances rejected at compile time" {
    // Non-associative subtraction fails Monoid associativity/identity law verification.
    try expectSemaError(
        \\pub trait Semigroup(a) {
        \\  fn combine(x: a, y: a) -> a
        \\  law assoc(x: a, y: a, z: a) { always combine(combine(x, y), z) == combine(x, combine(y, z)) }
        \\}
        \\pub trait Monoid(a) <= Semigroup(a) {
        \\  fn empty() -> a
        \\}
        \\pub default instance bad_sub: Monoid(u32) {
        \\  fn empty() -> u32 { 0u32 }
        \\  fn combine(x: u32, y: u32) -> u32 { x -| y }
        \\}
    , .law_violation);

    // Duplicate default instance for the same (trait, type) is ambiguous.
    try expectSemaError(
        \\pub trait Semigroup(a) {
        \\  fn combine(x: a, y: a) -> a
        \\}
        \\pub default instance s1: Semigroup(u32) {
        \\  fn combine(x: u32, y: u32) -> u32 { x +| y }
        \\}
        \\pub default instance s2: Semigroup(u32) {
        \\  fn combine(x: u32, y: u32) -> u32 { max(x, y) }
        \\}
    , .duplicate_decl);
}

test "4. Stage F: nested polynomial structural `using` without newtype & branded container coherence" {
    const nested_src: [:0]const u8 =
        \\pub trait Score(a) {
        \\  fn score(x: a) -> u32
        \\}
        \\pub type Foo { v: u32 }
        \\pub type Qux(a) { q: a }
        \\pub type Bar(a) { b: a }
        \\pub default instance score_foo: Score(Foo) {
        \\  fn score(x: Foo) -> u32 { x.v }
        \\}
        \\pub instance bonus_foo: Score(Foo) {
        \\  fn score(x: Foo) -> u32 { x.v +| 100u32 }
        \\}
        \\pub default instance score_qux: Score(Qux(a)) with Score(a) {
        \\  fn score(x: Qux(a)) -> u32 { score(x.q) }
        \\}
        \\pub default instance score_bar: Score(Bar(a)) with Score(a) {
        \\  fn score(x: Bar(a)) -> u32 { score(x.b) }
        \\}
        \\pub fn run_nested(bx: Bar(Qux(Foo))) -> u32 {
        \\  let d = score(bx)
        \\  let o = score(bx) using bonus_foo
        \\  d +| o
        \\}
    ;
    var res = try checkAndEmitAll(nested_src);
    defer {
        res.checked.deinit();
        res.tree.deinit();
        std.testing.allocator.free(res.mir_txt);
        std.testing.allocator.free(res.zig_txt);
        std.testing.allocator.free(res.rust_txt);
    }
    try std.testing.expect(std.mem.indexOf(u8, res.zig_txt, "__Inst_score_bar") != null);
    try std.testing.expect(std.mem.indexOf(u8, res.zig_txt, "__Inst_bonus_foo") != null);

    // Branded containers instantiated under sum_u32 vs max_u32 must not mix!
    try expectSemaError(
        \\pub trait Monoid(a) {
        \\  fn combine(x: a, y: a) -> a
        \\}
        \\pub default instance sum_u32: Monoid(u32) {
        \\  fn combine(x: u32, y: u32) -> u32 { x +| y }
        \\}
        \\pub instance max_u32: Monoid(u32) {
        \\  fn combine(x: u32, y: u32) -> u32 { max(x, y) }
        \\}
        \\pub type BrandedAcc(a) with Monoid(a) { val: a }
        \\fn make_acc(x: a) -> BrandedAcc(a) with Monoid(a) {
        \\  BrandedAcc { val: x }
        \\}
        \\fn bad_mix() -> BrandedAcc(u32) {
        \\  let mut b = make_acc(10u32)
        \\  let m = make_acc(20u32) using max_u32
        \\  b = m
        \\  b
        \\}
    , .type_mismatch);
}

test "5. Stage F: @external(rust), @layout(flat), packed-FFI rejection, physical SoA/AoSoA FFI codegen" {
    // Reject @layout(packed) / sub-byte fields across @external(rust)
    try expectSemaError(
        \\@layout(packed)
        \\pub type BitFlags { a: Int(0..=3), b: u8 }
        \\@external(rust, "take_flags")
        \\pub fn take_flags(f: BitFlags) -> u32
    , .invalid_ffi_type);

    const ecs_src: [:0]const u8 =
        \\@layout(flat)
        \\pub type StepConfig {
        \\  dt: f32,
        \\  gravity: f32,
        \\}
        \\@layout(soa)
        \\pub type Entity {
        \\  px: f32,
        \\  py: f32,
        \\  vx: f32,
        \\  vy: f32,
        \\}
        \\@layout(aosoa(8))
        \\pub type TileBody {
        \\  x: f32,
        \\  vx: f32,
        \\}
        \\@external(rust, "step_soa_physics")
        \\pub fn step_soa_physics(q: Collection(Entity) ~> mut .{px, vx}, cfg: StepConfig)
        \\@external(rust, "step_aosoa_bodies")
        \\pub fn step_aosoa_bodies(t: View(Collection(TileBody), Exclusive), dt: f32)
        \\pub fn main() -> f32 {
        \\  let mut ents: Collection(Entity) = [
        \\    Entity { px: 0.0f32, py: 0.0f32, vx: 2.0f32, vy: 0.0f32 },
        \\    Entity { px: 1.0f32, py: 0.0f32, vx: 3.0f32, vy: 0.0f32 },
        \\  ]
        \\  let mut tiles: Collection(TileBody) = [
        \\    TileBody { x: 0.0f32, vx: 4.0f32 },
        \\    TileBody { x: 1.0f32, vx: 5.0f32 },
        \\  ]
        \\  step_soa_physics(ents, StepConfig { dt: 0.5f32, gravity: 9.8f32 })
        \\  step_aosoa_bodies(tiles, 0.5f32)
        \\  ents[0].px + tiles[0].x
        \\}
    ;
    var res = try checkAndEmitAll(ecs_src);
    defer {
        res.checked.deinit();
        res.tree.deinit();
        std.testing.allocator.free(res.mir_txt);
        std.testing.allocator.free(res.zig_txt);
        std.testing.allocator.free(res.rust_txt);
    }

    try std.testing.expectEqual(@as(usize, 2), res.checked.foreign_contracts.len);
    try std.testing.expect(std.mem.indexOf(u8, res.zig_txt, "const StepConfig = extern struct") != null);
    try std.testing.expect(std.mem.indexOf(u8, res.zig_txt, "__AethelSoA_Entity") != null);
    try std.testing.expect(std.mem.indexOf(u8, res.zig_txt, "__AethelAoSoA_8_TileBody") != null);
    try std.testing.expect(std.mem.indexOf(u8, res.rust_txt, "pub struct StepConfig") != null);
    try std.testing.expect(std.mem.indexOf(u8, res.rust_txt, "pub struct Entity_px_vxQuery<'a>") != null);
    try std.testing.expect(std.mem.indexOf(u8, res.rust_txt, "pub struct TileBodyTile8") != null);
}

test "6. Stage F: offline Cargo crate staticlib compilation and @external(rust) instance + @layout(flat) bridge" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const io = std.testing.io;

    try Io.Dir.cwd().createDirPath(io, ".aethel-build/test_cargo_crate/src");
    defer Io.Dir.cwd().deleteTree(io, ".aethel-build/test_cargo_crate") catch {};
    defer Io.Dir.cwd().deleteFile(io, ".aethel-build/stage_f_cargo_test_rust_bridge.rs") catch {};
    defer Io.Dir.cwd().deleteFile(io, ".aethel-build/libstage_f_cargo_test_rust.a") catch {};

    try Io.Dir.cwd().writeFile(io, .{
        .sub_path = ".aethel-build/test_cargo_crate/Cargo.toml",
        .data =
        \\[package]
        \\name = "aethel-test-crate"
        \\version = "0.1.0"
        \\edition = "2021"
        \\
        ,
    });
    try Io.Dir.cwd().writeFile(io, .{
        .sub_path = ".aethel-build/test_cargo_crate/src/lib.rs",
        .data =
        \\#[repr(C)]
        \\#[derive(Copy, Clone)]
        \\pub struct FlatPair {
        \\    pub a: i32,
        \\    pub b: i32,
        \\}
        \\
        \\pub fn scale_pair(p: FlatPair, k: i32) -> FlatPair {
        \\    FlatPair { a: p.a * k, b: p.b * k }
        \\}
        \\
        \\pub struct RustCombiner;
        \\impl RustCombiner {
        \\    pub fn combine(x: u32, y: u32) -> u32 {
        \\        x.wrapping_add(y)
        \\    }
        \\}
        \\
        ,
    });

    const source: [:0]const u8 =
        \\@layout(flat)
        \\pub type FlatPair {
        \\  pub a: i32,
        \\  pub b: i32,
        \\}
        \\
        \\pub trait Semigroup(a) {
        \\  fn combine(x: a, y: a) -> a
        \\}
        \\
        \\@external(rust, "scale_pair")
        \\pub fn scale_pair(p: FlatPair, k: i32) -> FlatPair
        \\
        \\@external(rust, "RustCombiner", "combine")
        \\pub instance rust_u32_semi: Semigroup(u32)
    ;

    var tree = try parser.parse(std.testing.allocator, source);
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());

    var checked = try sema.analyze(std.testing.allocator, &tree);
    defer checked.deinit();
    try std.testing.expect(!checked.hasErrors());
    try std.testing.expectEqual(@as(usize, 2), checked.foreign_contracts.len);

    var stderr_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    defer stderr_buf.deinit();
    const lib_path_opt = try rust_ffi.compileRustStaticlib(
        io,
        arena,
        &tree,
        &checked,
        ".aethel-build/test_cargo_crate",
        "stage_f_cargo_test",
        &stderr_buf.writer,
    );
    if (lib_path_opt == null) {
        std.debug.print("compileRustStaticlib stderr:\n{s}\n", .{stderr_buf.written()});
    }
    try std.testing.expect(lib_path_opt != null);
    const bytes = try Io.Dir.cwd().readFileAllocOptions(
        io,
        lib_path_opt.?,
        arena,
        .limited(32 * 1024 * 1024),
        .of(u8),
        0,
    );
    try std.testing.expect(std.mem.startsWith(u8, bytes, "!<arch>\n"));
}
