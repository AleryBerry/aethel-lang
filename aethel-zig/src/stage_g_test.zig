const std = @import("std");
const Io = std.Io;
const build_options = @import("build_options");
const ast = @import("ast.zig");
const parser = @import("parser.zig");
const module_loader = @import("module_loader.zig");
const stdlib = @import("stdlib.zig");
const sema = @import("sema.zig");
const mir = @import("mir.zig");
const codegen_zig = @import("codegen_zig.zig");

const CompiledProgram = struct {
    loaded: module_loader.LoadedProgram,
    tree: ast.Ast,
    checked: sema.CheckedModule,
    mir_txt: []u8,
    zig_txt: []u8,

    fn deinit(self: *CompiledProgram) void {
        std.testing.allocator.free(self.zig_txt);
        std.testing.allocator.free(self.mir_txt);
        self.checked.deinit();
        self.tree.deinit();
        self.loaded.deinit();
    }
};

fn compileInMemoryMain(source: [:0]const u8) !CompiledProgram {
    const files = [_]module_loader.MemoryFile{
        .{ .module_key = "main", .path = "main.aethel", .source = source },
    };
    var loaded = try module_loader.loadFromMemory(std.testing.allocator, "main", &files);
    errdefer loaded.deinit();
    if (loaded.hasErrors()) {
        for (loaded.errors) |e| std.debug.print("load err: {s}\n", .{e.message});
        return error.UnexpectedLoadError;
    }

    var tree = try parser.parse(std.testing.allocator, loaded.combined_source);
    errdefer tree.deinit();
    if (tree.hasErrors()) {
        for (tree.diagnostics) |d| {
            const loc = std.fmt.allocPrint(std.testing.allocator, "parse err [{d}..{d}]: {s}", .{ d.span.start, d.span.end, d.message }) catch d.message;
            defer if (loc.ptr != d.message.ptr) std.testing.allocator.free(loc);
            const snippet_end = @min(loaded.combined_source.len, d.span.start + 60);
            const snippet_start = if (d.span.start > 30) d.span.start - 30 else 0;
            std.debug.print("{s} near `{s}`\n", .{ loc, loaded.combined_source[snippet_start..snippet_end] });
        }
        return error.UnexpectedParseError;
    }

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
    errdefer checked.deinit();
    if (checked.hasErrors()) {
        for (checked.diagnostics) |d| std.debug.print("sema err: {s}\n", .{d.message});
        return error.UnexpectedSemaError;
    }

    var mir_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    errdefer mir_buf.deinit();
    try mir.emitMir(&checked, &mir_buf.writer);

    var zig_buf: Io.Writer.Allocating = .init(std.testing.allocator);
    errdefer zig_buf.deinit();
    try codegen_zig.emitZig(&tree, &checked, &zig_buf.writer);

    return .{
        .loaded = loaded,
        .tree = tree,
        .checked = checked,
        .mir_txt = try mir_buf.toOwnedSlice(),
        .zig_txt = try zig_buf.toOwnedSlice(),
    };
}

fn expectProgramSemaError(source: [:0]const u8, expected: sema.SemaDiagnostic.Kind) !void {
    const files = [_]module_loader.MemoryFile{
        .{ .module_key = "main", .path = "main.aethel", .source = source },
    };
    var loaded = try module_loader.loadFromMemory(std.testing.allocator, "main", &files);
    defer loaded.deinit();
    try std.testing.expect(!loaded.hasErrors());

    var tree = try parser.parse(std.testing.allocator, loaded.combined_source);
    defer tree.deinit();
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
    for (checked.diagnostics) |d| {
        if (d.kind == expected) return;
    }
    std.debug.print("expected sema diagnostic {s}, got {d} diagnostic(s)\n", .{
        @tagName(expected),
        checked.diagnostics.len,
    });
    for (checked.diagnostics) |d| {
        std.debug.print("  got {s}: {s}\n", .{ @tagName(d.kind), d.message });
    }
    return error.ExpectedSemaErrorMissing;
}

test "1. Stage G: embedded stdlib parity with std/*.aethel & multi-import law checking" {
    const io = std.testing.io;
    const expected_modules = [_]struct { key: []const u8, file: []const u8 }{
        .{ .key = "std/cmp", .file = "cmp.aethel" },
        .{ .key = "std/traits", .file = "traits.aethel" },
        .{ .key = "std/option", .file = "option.aethel" },
        .{ .key = "std/result", .file = "result.aethel" },
        .{ .key = "std/math", .file = "math.aethel" },
        .{ .key = "std/str", .file = "str.aethel" },
        .{ .key = "std/io", .file = "io.aethel" },
        .{ .key = "std/vec", .file = "vec.aethel" },
        .{ .key = "std/map", .file = "map.aethel" },
        .{ .key = "std/set", .file = "set.aethel" },
        .{ .key = "std/deque", .file = "deque.aethel" },
    };
    for (expected_modules) |m| {
        const embedded = stdlib.lookup(m.key) orelse return error.MissingEmbeddedStdlib;
        const abs_path = try std.fmt.allocPrint(std.testing.allocator, "{s}/{s}", .{ build_options.std_dir, m.file });
        defer std.testing.allocator.free(abs_path);
        const on_disk = try Io.Dir.cwd().readFileAllocOptions(
            io,
            abs_path,
            std.testing.allocator,
            .limited(1024 * 1024),
            .of(u8),
            0,
        );
        defer std.testing.allocator.free(on_disk);
        try std.testing.expectEqualStrings(embedded, on_disk);
    }

    const src =
        \\import std/cmp as cmp
        \\import std/traits as traits
        \\import std/option as opt
        \\import std/result as res
        \\import std/math as math
        \\import std/str as str
        \\
        \\pub fn main() {
        \\  let scores: [u32] = [10, 20, 12]
        \\  let folded = traits.fold_slice(scores)
        \\  let o = Some(folded)
        \\  let v = opt.unwrap_or(o, 0)
        \\  let r: Result(u32, u32) = Ok(math.gcd_u32(v, 24))
        \\  let g = res.unwrap_or(r, 1)
        \\  let p = math.pow_u32(2, 5)
        \\  let ord = cmp.compare_u32(p, g)
        \\  let msg = "aethel-std"
        \\  if cmp.is_gt(ord) && str.starts_with(msg, "aethel") {
        \\    println("ok")
        \\  }
        \\}
    ;
    var prog = try compileInMemoryMain(src);
    defer prog.deinit();

    try std.testing.expect(prog.checked.laws.len > 0);
    for (prog.checked.laws) |law| {
        if (law.verdict == .falsified or law.verdict == .violated) {
            std.debug.print("unexpected law verdict for {s}: {s} ({s})\n", .{
                law.name,
                @tagName(law.verdict),
                law.tier_detail,
            });
            return error.UnexpectedLawVerdict;
        }
    }
}

test "2. Stage G: layout-polymorphic Vec SoA/AoSoA synthesis, dyn_vec MIR, SIMD & zero-copy borrow" {
    const src =
        \\import std/vec as vec
        \\
        \\@layout(soa)
        \\type Entity {
        \\  id: u32,
        \\  hp: u32,
        \\}
        \\
        \\@layout(aosoa(8))
        \\type Particle {
        \\  x: f32,
        \\  vx: f32,
        \\}
        \\
        \\fn heal_entities(es: Collection(Entity) ~>.{ hp }) -> u32 {
        \\  let mut total: u32 = 0
        \\  for e in es {
        \\    total = total + e.hp
        \\  }
        \\  total
        \\}
        \\
        \\pub fn main() {
        \\  let mut es: Vec(Entity) = vec.with_capacity(4)
        \\  vec.push(es, Entity { id: 1, hp: 50 })
        \\  vec.push(es, Entity { id: 2, hp: 75 })
        \\  let hsum = heal_entities(es)
        \\  vec.push(es, Entity { id: 3, hp: hsum })
        \\
        \\  let mut ps: Vec(Particle) = vec.new()
        \\  let mut i: u32 = 0
        \\  while i < 10 {
        \\    vec.push(ps, Particle { x: 1.0, vx: 2.0 })
        \\    i = i + 1
        \\  }
        \\  let total_x = ps
        \\    |> map_in_place(fn(p) { p.x = p.x + p.vx })
        \\    |> fold(0.0, fn(acc, p) { acc + p.x })
        \\  println(total_x, es[0].id)
        \\}
    ;
    var prog = try compileInMemoryMain(src);
    defer prog.deinit();

    try std.testing.expect(std.mem.indexOf(u8, prog.mir_txt, "dyn_vec Entity soa 2 8") != null);
    try std.testing.expect(std.mem.indexOf(u8, prog.mir_txt, "dyn_vec Particle aosoa 8 2 8") != null);
    try std.testing.expect(std.mem.indexOf(u8, prog.zig_txt, "__AethelDynSoA_Entity") != null);
    try std.testing.expect(std.mem.indexOf(u8, prog.zig_txt, "__AethelDynAoSoA_8_Particle") != null);
    try std.testing.expect(std.mem.indexOf(u8, prog.zig_txt, "@Vector(8, f32)") != null);
    try std.testing.expect(std.mem.indexOf(u8, prog.zig_txt, ".asView()") != null);
}

test "3. Stage G: borrow-reservation & ownership counterexamples + early-release witness" {
    // Counterexample 1: live range slice view across vec.push -> borrow_conflict
    try expectProgramSemaError(
        \\import std/vec as vec
        \\pub fn main() {
        \\  let mut xs: Vec(u32) = vec.new()
        \\  vec.push(xs, 10)
        \\  vec.push(xs, 20)
        \\  let sub = xs[0..1]
        \\  vec.push(xs, 30)
        \\  println(sub[0])
        \\}
    , .borrow_conflict);

    // Counterexample 2: live vec.as_slice across vec.push -> borrow_conflict
    try expectProgramSemaError(
        \\import std/vec as vec
        \\pub fn main() {
        \\  let mut xs: Vec(u32) = vec.new()
        \\  vec.push(xs, 1)
        \\  let sl = vec.as_slice(xs)
        \\  vec.push(xs, 2)
        \\  println(sl.len)
        \\}
    , .borrow_conflict);

    // Counterexample 3: live shared view of Map across map.insert -> borrow_conflict
    try expectProgramSemaError(
        \\import std/map as map
        \\pub fn main() {
        \\  let mut m: Map(u32, u32) = map.new()
        \\  map.put(m, 1, 10)
        \\  view shared v = m {
        \\    map.put(m, 2, 20)
        \\  }
        \\}
    , .borrow_conflict);

    // Counterexample 4: mutating immutable Vec -> mutability_error
    try expectProgramSemaError(
        \\import std/vec as vec
        \\pub fn main() {
        \\  let xs: Vec(u32) = vec.new()
        \\  vec.push(xs, 1)
        \\}
    , .mutability_error);

    // Counterexample 5: use after move -> use_after_move
    try expectProgramSemaError(
        \\import std/vec as vec
        \\pub fn main() {
        \\  let mut xs: Vec(u32) = vec.new()
        \\  vec.push(xs, 7)
        \\  let ys = xs
        \\  println(ys.len, xs.len)
        \\}
    , .use_after_move);

    // Positive witness: sub's last use finishes before vec.push -> auto-released safely
    var ok_prog = try compileInMemoryMain(
        \\import std/vec as vec
        \\pub fn main() {
        \\  let mut xs: Vec(u32) = vec.new()
        \\  vec.push(xs, 10)
        \\  let sub = vec.as_slice(xs)
        \\  let first = sub[0]
        \\  vec.push(xs, first +| 5)
        \\  println(xs.len)
        \\}
    );
    defer ok_prog.deinit();
}

test "4. Stage G: Map/Set/Deque codegen & unlawful f32 key rejection" {
    const ok_src =
        \\import std/vec as vec
        \\import std/map as map
        \\import std/set as set
        \\import std/deque as deque
        \\
        \\fn make_vec() -> Vec(u32) {
        \\  let mut xs: Vec(u32) = vec.new()
        \\  vec.push(xs, 1)
        \\  xs
        \\}
        \\
        \\pub fn main() {
        \\  let moved_v = make_vec()
        \\  let mut scores: Map(String, u32) = map.new()
        \\  map.put(scores, "alice", 42)
        \\  let has_alice = map.contains(scores, "alice")
        \\  let old = map.insert(scores, "alice", 99)
        \\
        \\  let mut seen: Set(u32) = set.new()
        \\  let added = set.insert(seen, 7)
        \\
        \\  let mut dq: Deque(i32) = deque.new()
        \\  deque.push_back(dq, 10)
        \\  deque.push_front(dq, -5)
        \\  println(moved_v.len, has_alice, added, old, dq.len)
        \\}
    ;
    var prog = try compileInMemoryMain(ok_src);
    defer prog.deinit();

    try std.testing.expect(std.mem.indexOf(u8, prog.zig_txt, "xs = .{};") != null);
    try std.testing.expect(std.mem.indexOf(u8, prog.zig_txt, "AethelMap([]const u8, u32)") != null);
    try std.testing.expect(std.mem.indexOf(u8, prog.zig_txt, "AethelSet(u32)") != null);
    try std.testing.expect(std.mem.indexOf(u8, prog.zig_txt, "AethelDeque(i32)") != null);
    try std.testing.expect(std.mem.indexOf(u8, prog.zig_txt, "aethel_gpa = init.gpa;") != null);
    try std.testing.expect(std.mem.indexOf(u8, prog.zig_txt, "defer scores.deinit();") != null);
    try std.testing.expect(std.mem.indexOf(u8, prog.zig_txt, "defer seen.deinit();") != null);
    try std.testing.expect(std.mem.indexOf(u8, prog.zig_txt, "defer dq.deinit();") != null);

    // Unlawful float Map key rejected (no Hash/Eq IEEE-754 NaN breach)
    try expectProgramSemaError(
        \\import std/map as map
        \\pub fn main() {
        \\  let mut bad: Map(f32, u32) = map.new()
        \\  map.put(bad, 1.0, 2)
        \\}
    , .type_mismatch);
}
