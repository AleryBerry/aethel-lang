const std = @import("std");
const lexer = @import("lexer.zig");

const Lexer = lexer.Lexer;
const Token = lexer.Token;

fn expectTokens(source: [:0]const u8, expected: []const struct { Token.Tag, []const u8 }) !void {
    const tokens = try Lexer.tokenizeAll(std.testing.allocator, source);
    defer std.testing.allocator.free(tokens);

    try std.testing.expectEqual(expected.len + 1, tokens.len);
    for (expected, 0..) |exp, idx| {
        const tok = tokens[idx];
        try std.testing.expectEqual(exp[0], tok.tag);
        try std.testing.expectEqualStrings(exp[1], tok.loc.slice(source));
    }
    try std.testing.expectEqual(Token.Tag.eof, tokens[expected.len].tag);
}

test "all hard reserved keywords and underscores/identifiers" {
    try expectTokens(
        "pub import as fn let mut const type opaque case if else while for in use return view move law extern true false todo panic _ _tmp foo_1 Entity Status",
        &.{
            .{ .kw_pub, "pub" },
            .{ .kw_import, "import" },
            .{ .kw_as, "as" },
            .{ .kw_fn, "fn" },
            .{ .kw_let, "let" },
            .{ .kw_mut, "mut" },
            .{ .kw_const, "const" },
            .{ .kw_type, "type" },
            .{ .kw_opaque, "opaque" },
            .{ .kw_case, "case" },
            .{ .kw_if, "if" },
            .{ .kw_else, "else" },
            .{ .kw_while, "while" },
            .{ .kw_for, "for" },
            .{ .kw_in, "in" },
            .{ .kw_use, "use" },
            .{ .kw_return, "return" },
            .{ .kw_view, "view" },
            .{ .kw_move, "move" },
            .{ .kw_law, "law" },
            .{ .kw_extern, "extern" },
            .{ .kw_true, "true" },
            .{ .kw_false, "false" },
            .{ .kw_todo, "todo" },
            .{ .kw_panic, "panic" },
            .{ .underscore, "_" },
            .{ .ident, "_tmp" },
            .{ .ident, "foo_1" },
            .{ .upper_ident, "Entity" },
            .{ .upper_ident, "Status" },
        },
    );
}

test "contextual keywords and arbitrary-width primitive types remain identifiers at token level" {
    const src: [:0]const u8 =
        "always never preserves when decreases layout aos soa aosoa packed shared exclusive fork join " ++
        "u1 u2 u3 u4 u8 u16 u24 u32 u64 u128 u65535 i1 i2 i4 i7 i8 i16 i24 i32 i64 i65535 f32 f64 bool";
    const tokens = try Lexer.tokenizeAll(std.testing.allocator, src);
    defer std.testing.allocator.free(tokens);

    for (tokens[0 .. tokens.len - 1], 0..) |tok, idx| {
        try std.testing.expectEqual(Token.Tag.ident, tok.tag);
        const lexeme = tok.loc.slice(src);
        if (idx < 14) {
            try std.testing.expect(lexer.contextualKeyword(lexeme) != null);
        } else {
            try std.testing.expect(lexer.parsePrimitiveType(lexeme) != null);
        }
    }
    try std.testing.expectEqual(lexer.PrimitiveType{ .unsigned = 4 }, lexer.parsePrimitiveType("u4").?);
    try std.testing.expectEqual(lexer.PrimitiveType{ .signed = 7 }, lexer.parsePrimitiveType("i7").?);
    try std.testing.expectEqual(lexer.PrimitiveType{ .signed = 64 }, lexer.parsePrimitiveType("i64").?);
    try std.testing.expectEqual(lexer.PrimitiveType{ .unsigned = 128 }, lexer.parsePrimitiveType("u128").?);
    try std.testing.expectEqual(lexer.PrimitiveType{ .unsigned = 65535 }, lexer.parsePrimitiveType("u65535").?);
    try std.testing.expectEqual(lexer.PrimitiveType.f32, lexer.parsePrimitiveType("f32").?);
    try std.testing.expectEqual(lexer.PrimitiveType.bool, lexer.parsePrimitiveType("bool").?);

    try std.testing.expect(lexer.contextualKeyword("regular_var") == null);
    try std.testing.expect(lexer.parsePrimitiveType("u0") == null);
    try std.testing.expect(lexer.parsePrimitiveType("i0") == null);
    try std.testing.expect(lexer.parsePrimitiveType("u08") == null);
    try std.testing.expect(lexer.parsePrimitiveType("i07") == null);
    try std.testing.expect(lexer.parsePrimitiveType("u65536") == null);
    try std.testing.expect(lexer.parsePrimitiveType("i99999") == null);
    try std.testing.expect(lexer.parsePrimitiveType("u") == null);
    try std.testing.expect(lexer.parsePrimitiveType("u7x") == null);
}

test "all delimiters, arrows, pipelines, and arithmetic/wrapping/saturating operators" {
    try expectTokens(
        "( ) { } [ ] , : ; . .. ..= @ ? ~> |> -> <- => + += +% +| - -= -% -| * *= *% *| / /= % %= = == ! != < <= << <> > >= >> & && | || ^ ~",
        &.{
            .{ .l_paren, "(" },
            .{ .r_paren, ")" },
            .{ .l_brace, "{" },
            .{ .r_brace, "}" },
            .{ .l_bracket, "[" },
            .{ .r_bracket, "]" },
            .{ .comma, "," },
            .{ .colon, ":" },
            .{ .semicolon, ";" },
            .{ .dot, "." },
            .{ .dot_dot, ".." },
            .{ .dot_dot_eq, "..=" },
            .{ .at, "@" },
            .{ .question, "?" },
            .{ .tilde_arrow, "~>" },
            .{ .pipe, "|>" },
            .{ .arrow, "->" },
            .{ .left_arrow, "<-" },
            .{ .fat_arrow, "=>" },
            .{ .plus, "+" },
            .{ .plus_eq, "+=" },
            .{ .plus_percent, "+%" },
            .{ .plus_pipe, "+|" },
            .{ .minus, "-" },
            .{ .minus_eq, "-=" },
            .{ .minus_percent, "-%" },
            .{ .minus_pipe, "-|" },
            .{ .star, "*" },
            .{ .star_eq, "*=" },
            .{ .star_percent, "*%" },
            .{ .star_pipe, "*|" },
            .{ .slash, "/" },
            .{ .slash_eq, "/=" },
            .{ .percent, "%" },
            .{ .percent_eq, "%=" },
            .{ .eq, "=" },
            .{ .eq_eq, "==" },
            .{ .bang, "!" },
            .{ .bang_eq, "!=" },
            .{ .lt, "<" },
            .{ .lt_eq, "<=" },
            .{ .lt_lt, "<<" },
            .{ .lt_gt, "<>" },
            .{ .gt, ">" },
            .{ .gt_eq, ">=" },
            .{ .gt_gt, ">>" },
            .{ .amp, "&" },
            .{ .amp_amp, "&&" },
            .{ .bar, "|" },
            .{ .pipe_pipe, "||" },
            .{ .caret, "^" },
            .{ .tilde, "~" },
        },
    );
}

test "comments, CRLF doc comments, and comment at EOF" {
    try expectTokens(
        "//// Module docs\r\n/// Item doc α\r\n// ignored plain comment\nlet x = 1 // trailing comment without newline",
        &.{
            .{ .module_doc_comment, "//// Module docs" },
            .{ .doc_comment, "/// Item doc α" },
            .{ .kw_let, "let" },
            .{ .ident, "x" },
            .{ .eq, "=" },
            .{ .int_literal, "1" },
        },
    );
    try expectTokens("/// doc at EOF", &.{.{ .doc_comment, "/// doc at EOF" }});
    try expectTokens("////", &.{.{ .module_doc_comment, "////" }});
}

test "numbers, ranges, method calls, hex exponent trap, and suffix-free literals" {
    try expectTokens(
        "0..10 1..=5 10.to_u8 0x10e2 0b1010_0101 0o755 0xff 1_000_000 42 as i7 3.14 2.5e-3 1e+10 0.0 1e2+3",
        &.{
            .{ .int_literal, "0" },
            .{ .dot_dot, ".." },
            .{ .int_literal, "10" },
            .{ .int_literal, "1" },
            .{ .dot_dot_eq, "..=" },
            .{ .int_literal, "5" },
            .{ .int_literal, "10" },
            .{ .dot, "." },
            .{ .ident, "to_u8" },
            .{ .int_literal, "0x10e2" },
            .{ .int_literal, "0b1010_0101" },
            .{ .int_literal, "0o755" },
            .{ .int_literal, "0xff" },
            .{ .int_literal, "1_000_000" },
            .{ .int_literal, "42" },
            .{ .kw_as, "as" },
            .{ .ident, "i7" },
            .{ .float_literal, "3.14" },
            .{ .float_literal, "2.5e-3" },
            .{ .float_literal, "1e+10" },
            .{ .float_literal, "0.0" },
            .{ .float_literal, "1e2" },
            .{ .plus, "+" },
            .{ .int_literal, "3" },
        },
    );
}

test "malformed numbers and glued suffixes produce invalid_number and keep scanning aligned" {
    try expectTokens(
        "0x 0b102 0o78 1__0 1_ 1.5_ 1_.5 1e+ 123abc 1.5u8 42u0 42u08 42u65536 42i7 0b1010_0101u8 3.14f32 1_u65535 next_tok",
        &.{
            .{ .invalid_number, "0x" },
            .{ .invalid_number, "0b102" },
            .{ .invalid_number, "0o78" },
            .{ .invalid_number, "1__0" },
            .{ .invalid_number, "1_" },
            .{ .invalid_number, "1.5_" },
            .{ .invalid_number, "1_.5" },
            .{ .invalid_number, "1e+" },
            .{ .invalid_number, "123abc" },
            .{ .invalid_number, "1.5u8" },
            .{ .invalid_number, "42u0" },
            .{ .invalid_number, "42u08" },
            .{ .invalid_number, "42u65536" },
            .{ .invalid_number, "42i7" },
            .{ .invalid_number, "0b1010_0101u8" },
            .{ .invalid_number, "3.14f32" },
            .{ .invalid_number, "1_u65535" },
            .{ .ident, "next_tok" },
        },
    );
}

test "string escapes, Unicode scalars, surrogates, and string error recovery" {
    try expectTokens(
        "\"hello\\n\\t\\\"\\\\\\0\\x41\\u{1F600}\" \"\\q\" \"\\u{D800}\" \"\\u{110000}\" \"\\u{}\" \"unterminated",
        &.{
            .{ .string_literal, "\"hello\\n\\t\\\"\\\\\\0\\x41\\u{1F600}\"" },
            .{ .invalid_escape, "\"\\q\"" },
            .{ .invalid_escape, "\"\\u{D800}\"" },
            .{ .invalid_escape, "\"\\u{110000}\"" },
            .{ .invalid_escape, "\"\\u{}\"" },
            .{ .unterminated_string, "\"unterminated" },
        },
    );
}

test "UTF-8 BOM, stray Unicode symbol, malformed UTF-8, and embedded NUL byte" {
    const bom_src: [:0]const u8 = "\xEF\xBB\xBFlet a = 1";
    try expectTokens(bom_src, &.{
        .{ .kw_let, "let" },
        .{ .ident, "a" },
        .{ .eq, "=" },
        .{ .int_literal, "1" },
    });

    const bad_src: [:0]const u8 = "a \xCE\xBB \xFF \x00 b";
    try expectTokens(bad_src, &.{
        .{ .ident, "a" },
        .{ .invalid_char, "\xCE\xBB" },
        .{ .invalid_utf8, "\xFF" },
        .{ .invalid_char, "\x00" },
        .{ .ident, "b" },
    });
}

test "computeLineCol and peek accuracy across LF, CRLF, and BOM" {
    const src: [:0]const u8 = "\xEF\xBB\xBFfn step(x: u8) {\r\n  let α = x\n}";
    var lex = Lexer.init(src);

    const p1 = lex.peek();
    const n1 = lex.next();
    try std.testing.expectEqual(p1, n1);
    const lc1 = lexer.computeLineCol(src, n1.loc.start);
    try std.testing.expectEqual(@as(usize, 1), lc1.line);
    try std.testing.expectEqual(@as(usize, 1), lc1.column);
    try std.testing.expectEqualStrings("fn step(x: u8) {", src[lc1.line_start..lc1.line_end]);

    const tokens = try Lexer.tokenizeAll(std.testing.allocator, src);
    defer std.testing.allocator.free(tokens);

    // Find `=` on line 2 (`  let α = x`): byte col vs UTF-8 col (`  let α ` -> 8 codepoints => col 9)
    var eq_tok: ?Token = null;
    for (tokens) |tok| {
        if (tok.tag == .eq) eq_tok = tok;
    }
    const lc_eq = lexer.computeLineCol(src, eq_tok.?.loc.start);
    try std.testing.expectEqual(@as(usize, 2), lc_eq.line);
    try std.testing.expectEqual(@as(usize, 9), lc_eq.column);
    try std.testing.expectEqualStrings("  let α = x", src[lc_eq.line_start..lc_eq.line_end]);
}

test "realistic Aethel program with path borrows, Tiled AoSoA annotation, and laws.aethel" {
    const src: [:0]const u8 =
        \\pub fn update_motion(entities: Collection(Entity) ~>.{pos, vel}, dt: u16) -> u16 {
        \\  @layout(aosoa(8))
        \\  entities |> map_in_place(fn(e) { e.pos = e.pos +% e.vel * dt })
        \\}
        \\law movement_safe(e: View(Entity, Exclusive), dt: u16) {
        \\  preserves e.health, e.team
        \\}
    ;
    const tokens = try Lexer.tokenizeAll(std.testing.allocator, src);
    defer std.testing.allocator.free(tokens);

    for (tokens) |tok| {
        try std.testing.expect(!tok.tag.isError());
    }
    // Verify key path-borrow sequence `~> . { pos , vel }`
    var found_tilde_arrow = false;
    for (tokens, 0..) |tok, idx| {
        if (tok.tag == .tilde_arrow) {
            found_tilde_arrow = true;
            try std.testing.expectEqual(Token.Tag.dot, tokens[idx + 1].tag);
            try std.testing.expectEqual(Token.Tag.l_brace, tokens[idx + 2].tag);
            try std.testing.expectEqualStrings("pos", tokens[idx + 3].loc.slice(src));
            try std.testing.expectEqual(Token.Tag.comma, tokens[idx + 4].tag);
            try std.testing.expectEqualStrings("vel", tokens[idx + 5].loc.slice(src));
            try std.testing.expectEqual(Token.Tag.r_brace, tokens[idx + 6].tag);
        }
    }
    try std.testing.expect(found_tilde_arrow);
}

test "fuzz/invariant property: strict forward progress, bounded spans, and idempotent EOF" {
    try std.testing.fuzz({}, fuzzLexerInvariants, .{});
}

fn fuzzLexerInvariants(_: void, smith: *std.testing.Smith) !void {
    const gpa = std.testing.allocator;
    const raw_len: usize = smith.valueRangeAtMost(u16, 0, 256);
    const buf = try gpa.allocSentinel(u8, raw_len, 0);
    defer gpa.free(buf);
    smith.bytes(buf[0..raw_len]);

    var lex = Lexer.init(buf);
    var prev_end: usize = lex.index;
    var count: usize = 0;

    while (true) {
        const tok = lex.next();
        count += 1;
        try std.testing.expect(count <= buf.len + 2);
        try std.testing.expect(tok.loc.start <= tok.loc.end);
        try std.testing.expect(tok.loc.end <= buf.len);

        if (tok.tag == .eof) {
            try std.testing.expectEqual(buf.len, tok.loc.start);
            try std.testing.expectEqual(buf.len, tok.loc.end);
            const eof_again = lex.next();
            try std.testing.expectEqual(Token.Tag.eof, eof_again.tag);
            break;
        }
        try std.testing.expect(tok.loc.end > prev_end);
        prev_end = tok.loc.end;
    }
}
