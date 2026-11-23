const std = @import("std");
const ast = @import("ast.zig");
const parser = @import("parser.zig");
const sema = @import("sema.zig");
const mir = @import("mir.zig");

fn analyzeSource(src: [:0]const u8) !struct { tree: ast.Ast, checked: sema.CheckedModule } {
    var tree = try parser.parse(std.testing.allocator, src);
    errdefer tree.deinit();
    if (tree.hasErrors()) return error.UnexpectedParseError;
    const checked = try sema.analyze(std.testing.allocator, &tree);
    return .{ .tree = tree, .checked = checked };
}

test "1. Stage D Tier 1 exhaustive proof and minimal counterexample falsification" {
    // Valid exhaustive law over u8 calling pure helper function (256 * 256 = 65536 states)
    {
        var res = try analyzeSource(
            \\fn sat_sub(hp: u8, dmg: u8) -> u8 { hp -| dmg }
            \\law bounded_damage_u8(hp: u8, dmg: u8) {
            \\  always sat_sub(hp, dmg) <= hp
            \\  always hp -| hp == 0u8
            \\}
        );
        defer res.tree.deinit();
        defer res.checked.deinit();
        try std.testing.expect(!res.checked.hasErrors());
        try std.testing.expectEqual(@as(usize, 1), res.checked.laws.len);
        // `hp -| dmg <= hp` and `hp -| hp == 0` are proved symbolically at Tier 2!
        try std.testing.expectEqual(sema.LawVerdict.proved_tier2_symbolic, res.checked.laws[0].verdict);
        try std.testing.expectEqual(@as(usize, 2), res.checked.laws[0].symbolic_certs.len);
    }

    // Pure Tier 1 exhaustive proof on finite Int(0..=15) bitwise invariant outside Tier 2 linear arithmetic
    {
        var res = try analyzeSource(
            \\fn mask_low(x: Int(0..=15), m: Int(0..=7)) -> Int(0..=15) {
            \\  x & m
            \\}
            \\law mask_shrinks(x: Int(0..=15), m: Int(0..=7)) {
            \\  always mask_low(x, m) <= m
            \\}
        );
        defer res.tree.deinit();
        defer res.checked.deinit();
        try std.testing.expect(!res.checked.hasErrors());
        try std.testing.expectEqual(sema.LawVerdict.proved_tier1_exhaustive, res.checked.laws[0].verdict);
    }

    // Buggy wrapping damage law falsified with concrete minimal counterexample (hp = 0, dmg = 1)
    {
        var res = try analyzeSource(
            \\fn buggy_sub(hp: u8, dmg: u8) -> u8 { hp -% dmg }
            \\law bad_wrapping_damage(hp: u8, dmg: u8) {
            \\  always buggy_sub(hp, dmg) <= hp
            \\}
        );
        defer res.tree.deinit();
        defer res.checked.deinit();
        try std.testing.expect(res.checked.hasErrors());
        try std.testing.expectEqual(sema.LawVerdict.falsified, res.checked.laws[0].verdict);
        try std.testing.expect(res.checked.laws[0].counterexample != null);
        try std.testing.expectEqualStrings("hp = 0, dmg = 1", res.checked.laws[0].counterexample.?);
    }
}

test "2. Stage D Tier 2 symbolic laws (damage_recovery, add_comm, min_le_add) and MIR emission" {
    const src =
        \\law damage_recovery(hp: u32, dmg: u32) {
        \\  when dmg <= hp
        \\  always (hp -| dmg) + dmg == hp
        \\}
        \\law add_comm(x: u32, y: u32) {
        \\  always x + y == y + x
        \\}
        \\law min_le_add(a: u32, b: u32, c: u32) {
        \\  always min(a, b) <= a + c
        \\}
    ;
    var res = try analyzeSource(src);
    defer res.tree.deinit();
    defer res.checked.deinit();
    try std.testing.expect(!res.checked.hasErrors());
    try std.testing.expectEqual(@as(usize, 3), res.checked.laws.len);
    for (res.checked.laws) |law| {
        try std.testing.expectEqual(sema.LawVerdict.proved_tier2_symbolic, law.verdict);
        try std.testing.expectEqual(@as(usize, 1), law.symbolic_certs.len);
    }

    var mir_buf: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer mir_buf.deinit();
    try mir.emitMir(&res.checked, &mir_buf.writer);
    const mir_text = mir_buf.written();
    try std.testing.expect(std.mem.indexOf(u8, mir_text, "law_always damage_recovery") != null);
    try std.testing.expect(std.mem.indexOf(u8, mir_text, "hyp le v1 v0") != null);
    try std.testing.expect(std.mem.indexOf(u8, mir_text, "goal eq add sub v0 v1 v1 v0") != null);
    try std.testing.expect(std.mem.indexOf(u8, mir_text, "law_always min_le_add") != null);
}

test "3. Stage D termination decreases verification on while loops and recursive functions + MIR" {
    // Valid terminating while loop + recursive function
    {
        const src =
            \\fn sum_down(mut n: u32) -> u32 {
            \\  let mut acc: u32 = 0u32
            \\  while n > 0u32 decreases n {
            \\    acc = acc +% n
            \\    n = n - 1u32
            \\  }
            \\  acc
            \\}
            \\fn rec_countdown(n: u32) -> u32 decreases n {
            \\  if n == 0u32 {
            \\    0u32
            \\  } else {
            \\    1u32 +% rec_countdown(n - 1u32)
            \\  }
            \\}
        ;
        var res = try analyzeSource(src);
        defer res.tree.deinit();
        defer res.checked.deinit();
        try std.testing.expect(!res.checked.hasErrors());
        try std.testing.expectEqual(@as(usize, 1), res.checked.functions[0].decreases_certs.len);
        try std.testing.expectEqual(@as(usize, 1), res.checked.functions[1].decreases_certs.len);

        var mir_buf: std.Io.Writer.Allocating = .init(std.testing.allocator);
        defer mir_buf.deinit();
        try mir.emitMir(&res.checked, &mir_buf.writer);
        const mir_text = mir_buf.written();
        try std.testing.expect(std.mem.indexOf(u8, mir_text, "decreases 1 lt 0 v0 v0 sub v0 1") != null);
        try std.testing.expect(std.mem.indexOf(u8, mir_text, "ne v0 0 v0 sub v0 1") != null);
    }

    // Non-decreasing loop rejected with .termination_error
    {
        var res = try analyzeSource(
            \\fn bad_loop(mut n: u32) {
            \\  while n < 10u32 decreases n {
            \\    n = n + 1u32
            \\  }
            \\}
        );
        defer res.tree.deinit();
        defer res.checked.deinit();
        try std.testing.expect(res.checked.hasErrors());
        try std.testing.expectEqual(sema.SemaDiagnostic.Kind.termination_error, res.checked.diagnostics[0].kind);
    }

    // Non-decreasing recursive call rejected with .termination_error
    {
        var res = try analyzeSource(
            \\fn bad_rec(n: u32) -> u32 decreases n {
            \\  if n > 0u32 {
            \\    bad_rec(n)
            \\  } else {
            \\    0u32
            \\  }
            \\}
        );
        defer res.tree.deinit();
        defer res.checked.deinit();
        try std.testing.expect(res.checked.hasErrors());
        try std.testing.expectEqual(sema.SemaDiagnostic.Kind.termination_error, res.checked.diagnostics[0].kind);
    }
}
