const std = @import("std");

/// Byte slice span within a sentinel-terminated source buffer (`source[start..end]`).
pub const Loc = struct {
    start: usize,
    end: usize,

    pub fn slice(self: Loc, source: []const u8) []const u8 {
        return source[self.start..self.end];
    }

    pub fn len(self: Loc) usize {
        return self.end - self.start;
    }
};

/// 1-based line and UTF-8 scalar column coordinates, plus enclosing line bounds
/// (excluding any trailing `\r` / `\n`) for clean caret diagnostics.
pub const LineCol = struct {
    line: usize,
    column: usize,
    line_start: usize,
    line_end: usize,
};

pub fn computeLineCol(source: []const u8, raw_offset: usize) LineCol {
    const offset = @min(raw_offset, source.len);
    const bom_len: usize = if (source.len >= 3 and std.mem.eql(u8, source[0..3], "\xEF\xBB\xBF")) 3 else 0;

    var line: usize = 1;
    var line_start: usize = if (offset >= bom_len) bom_len else 0;

    var i: usize = line_start;
    while (i < offset) : (i += 1) {
        if (source[i] == '\n') {
            line += 1;
            line_start = i + 1;
        }
    }

    // Count 1-based UTF-8 codepoint columns from `line_start` up to `offset`.
    var col: usize = 1;
    var j: usize = line_start;
    while (j < offset) : (j += 1) {
        if ((source[j] & 0xC0) != 0x80) {
            col += 1;
        }
    }

    var line_end: usize = line_start;
    while (line_end < source.len and source[line_end] != '\n') : (line_end += 1) {}
    if (line_end > line_start and source[line_end - 1] == '\r') {
        line_end -= 1;
    }

    return .{
        .line = line,
        .column = col,
        .line_start = line_start,
        .line_end = line_end,
    };
}

/// Complete token descriptor pairing its syntactic category and source byte span.
pub const Token = struct {
    tag: Tag,
    loc: Loc,

    pub const Tag = enum {
        eof,

        // Diagnostic tokens (strict forward progress guaranteed on every error)
        invalid_char,
        invalid_utf8,
        invalid_number,
        unterminated_string,
        invalid_escape,

        // Documentation comments (`///` and `////`; plain `//` comments are skipped)
        doc_comment,
        module_doc_comment,

        // Identifiers and standalone underscore
        ident,
        upper_ident,
        underscore,

        // Literals
        int_literal,
        float_literal,
        string_literal,

        // Hard reserved keywords
        kw_pub,
        kw_import,
        kw_as,
        kw_fn,
        kw_let,
        kw_mut,
        kw_const,
        kw_type,
        kw_opaque,
        kw_case,
        kw_if,
        kw_else,
        kw_while,
        kw_for,
        kw_in,
        kw_use,
        kw_return,
        kw_view,
        kw_move,
        kw_law,
        kw_extern,
        kw_true,
        kw_false,
        kw_todo,
        kw_panic,

        // Delimiters & punctuation
        l_paren,
        r_paren,
        l_brace,
        r_brace,
        l_bracket,
        r_bracket,
        comma,
        colon,
        semicolon,
        dot,
        dot_dot,
        dot_dot_eq,
        at,
        question,

        // Arrows & pipelines
        tilde_arrow, // ~>
        pipe, // |>
        arrow, // ->
        left_arrow, // <-
        fat_arrow, // =>

        // Operators & assignment
        plus,
        plus_eq,
        plus_percent, // +%
        plus_pipe, // +|
        minus,
        minus_eq,
        minus_percent, // -%
        minus_pipe, // -|
        star,
        star_eq,
        star_percent, // *%
        star_pipe, // *|
        slash,
        slash_eq,
        percent,
        percent_eq,
        eq,
        eq_eq,
        bang,
        bang_eq,
        lt,
        lt_eq,
        lt_lt, // <<
        lt_gt, // <>
        gt,
        gt_eq,
        gt_gt, // >>
        amp,
        amp_amp,
        bar,
        pipe_pipe,
        caret,
        tilde,

        pub fn isError(self: Tag) bool {
            return switch (self) {
                .invalid_char, .invalid_utf8, .invalid_number, .unterminated_string, .invalid_escape => true,
                else => false,
            };
        }

        pub fn symbol(self: Tag) []const u8 {
            return switch (self) {
                .eof => "<eof>",
                .invalid_char => "<invalid_char>",
                .invalid_utf8 => "<invalid_utf8>",
                .invalid_number => "<invalid_number>",
                .unterminated_string => "<unterminated_string>",
                .invalid_escape => "<invalid_escape>",
                .doc_comment => "///",
                .module_doc_comment => "////",
                .ident => "<ident>",
                .upper_ident => "<upper_ident>",
                .underscore => "_",
                .int_literal => "<int>",
                .float_literal => "<float>",
                .string_literal => "<string>",
                .kw_pub => "pub",
                .kw_import => "import",
                .kw_as => "as",
                .kw_fn => "fn",
                .kw_let => "let",
                .kw_mut => "mut",
                .kw_const => "const",
                .kw_type => "type",
                .kw_opaque => "opaque",
                .kw_case => "case",
                .kw_if => "if",
                .kw_else => "else",
                .kw_while => "while",
                .kw_for => "for",
                .kw_in => "in",
                .kw_use => "use",
                .kw_return => "return",
                .kw_view => "view",
                .kw_move => "move",
                .kw_law => "law",
                .kw_extern => "extern",
                .kw_true => "true",
                .kw_false => "false",
                .kw_todo => "todo",
                .kw_panic => "panic",
                .l_paren => "(",
                .r_paren => ")",
                .l_brace => "{",
                .r_brace => "}",
                .l_bracket => "[",
                .r_bracket => "]",
                .comma => ",",
                .colon => ":",
                .semicolon => ";",
                .dot => ".",
                .dot_dot => "..",
                .dot_dot_eq => "..=",
                .at => "@",
                .question => "?",
                .tilde_arrow => "~>",
                .pipe => "|>",
                .arrow => "->",
                .left_arrow => "<-",
                .fat_arrow => "=>",
                .plus => "+",
                .plus_eq => "+=",
                .plus_percent => "+%",
                .plus_pipe => "+|",
                .minus => "-",
                .minus_eq => "-=",
                .minus_percent => "-%",
                .minus_pipe => "-|",
                .star => "*",
                .star_eq => "*=",
                .star_percent => "*%",
                .star_pipe => "*|",
                .slash => "/",
                .slash_eq => "/=",
                .percent => "%",
                .percent_eq => "%=",
                .eq => "=",
                .eq_eq => "==",
                .bang => "!",
                .bang_eq => "!=",
                .lt => "<",
                .lt_eq => "<=",
                .lt_lt => "<<",
                .lt_gt => "<>",
                .gt => ">",
                .gt_eq => ">=",
                .gt_gt => ">>",
                .amp => "&",
                .amp_amp => "&&",
                .bar => "|",
                .pipe_pipe => "||",
                .caret => "^",
                .tilde => "~",
            };
        }
    };
};

pub const keywords = std.StaticStringMap(Token.Tag).initComptime(.{
    .{ "pub", .kw_pub },
    .{ "import", .kw_import },
    .{ "as", .kw_as },
    .{ "fn", .kw_fn },
    .{ "let", .kw_let },
    .{ "mut", .kw_mut },
    .{ "const", .kw_const },
    .{ "type", .kw_type },
    .{ "opaque", .kw_opaque },
    .{ "case", .kw_case },
    .{ "if", .kw_if },
    .{ "else", .kw_else },
    .{ "while", .kw_while },
    .{ "for", .kw_for },
    .{ "in", .kw_in },
    .{ "use", .kw_use },
    .{ "return", .kw_return },
    .{ "view", .kw_view },
    .{ "move", .kw_move },
    .{ "law", .kw_law },
    .{ "extern", .kw_extern },
    .{ "true", .kw_true },
    .{ "false", .kw_false },
    .{ "todo", .kw_todo },
    .{ "panic", .kw_panic },
});

/// Contextual keywords kept as `.ident` at the token level so they remain usable
/// inside ordinary identifier positions when unambiguous in the grammar.
pub const ContextualKeyword = enum {
    always,
    never,
    preserves,
    when,
    decreases,
    layout,
    aos,
    soa,
    aosoa,
    auto,
    once,
    @"packed",
    shared,
    exclusive,
    fork,
    join,
    trait,
    instance,
    default,
    with,
    using,
    external,
    rust,
    flat,
};

pub const contextual_keywords = std.StaticStringMap(ContextualKeyword).initComptime(.{
    .{ "always", .always },
    .{ "never", .never },
    .{ "preserves", .preserves },
    .{ "when", .when },
    .{ "decreases", .decreases },
    .{ "layout", .layout },
    .{ "aos", .aos },
    .{ "soa", .soa },
    .{ "aosoa", .aosoa },
    .{ "auto", .auto },
    .{ "once", .once },
    .{ "packed", .@"packed" },
    .{ "shared", .shared },
    .{ "exclusive", .exclusive },
    .{ "fork", .fork },
    .{ "join", .join },
    .{ "trait", .trait },
    .{ "instance", .instance },
    .{ "default", .default },
    .{ "with", .with },
    .{ "using", .using },
    .{ "external", .external },
    .{ "rust", .rust },
    .{ "flat", .flat },
});

pub fn contextualKeyword(lexeme: []const u8) ?ContextualKeyword {
    return contextual_keywords.get(lexeme);
}

/// Maximum supported integer bit width (`1..=65535`), aligned with `Aethel.maxIntegerBits`.
pub const max_int_bits: u16 = 65535;

pub const IntWidth = struct {
    signed: bool,
    bits: u16,
};

/// Parse arbitrary-bit-width scalar integer spellings (`u1..u65535` or `i1..i65535`).
/// Rejects `u0`, `i0`, leading zeroes (`u08`, `i07`), and widths above `65535`.
pub fn parseIntWidth(lexeme: []const u8) ?IntWidth {
    if (lexeme.len < 2 or lexeme.len > 6) return null;
    const signed: bool = switch (lexeme[0]) {
        'u' => false,
        'i' => true,
        else => return null,
    };
    const digits = lexeme[1..];
    if (digits[0] < '1' or digits[0] > '9') return null;

    var acc: u32 = 0;
    for (digits) |b| {
        if (b < '0' or b > '9') return null;
        acc = acc * 10 + @as(u32, b - '0');
        if (acc > max_int_bits) return null;
    }
    return .{ .signed = signed, .bits = @intCast(acc) };
}

/// Arbitrary-bit-width integer and scalar primitive names from the formal spec.
/// Lexed as `.ident` so variable names like `i1`, `i2`, `u1`, `i7` work normally.
pub const PrimitiveType = union(enum) {
    unsigned: u16, // 1..=65535
    signed: u16, // 1..=65535
    f32,
    f64,
    bool,
};

pub fn parsePrimitiveType(lexeme: []const u8) ?PrimitiveType {
    if (parseIntWidth(lexeme)) |iw| {
        return if (iw.signed) .{ .signed = iw.bits } else .{ .unsigned = iw.bits };
    }
    if (std.mem.eql(u8, lexeme, "f32")) return .f32;
    if (std.mem.eql(u8, lexeme, "f64")) return .f64;
    if (std.mem.eql(u8, lexeme, "bool")) return .bool;
    return null;
}

/// Zero-allocation, sentinel-terminated streaming lexer for Aethel source buffers.
pub const Lexer = struct {
    source: [:0]const u8,
    index: usize,

    pub fn init(source: [:0]const u8) Lexer {
        const start_idx: usize = if (source.len >= 3 and std.mem.eql(u8, source[0..3], "\xEF\xBB\xBF")) 3 else 0;
        return .{
            .source = source,
            .index = start_idx,
        };
    }

    pub fn peek(self: *const Lexer) Token {
        var copy = self.*;
        return copy.next();
    }

    pub fn tokenizeAll(allocator: std.mem.Allocator, source: [:0]const u8) std.mem.Allocator.Error![]Token {
        var lex = Lexer.init(source);
        var list: std.ArrayList(Token) = .empty;
        errdefer list.deinit(allocator);
        while (true) {
            const tok = lex.next();
            try list.append(allocator, tok);
            if (tok.tag == .eof) break;
        }
        return try list.toOwnedSlice(allocator);
    }

    pub fn next(self: *Lexer) Token {
        while (true) {
            self.skipWhitespace();
            if (self.index >= self.source.len) {
                return .{ .tag = .eof, .loc = .{ .start = self.source.len, .end = self.source.len } };
            }

            const start = self.index;
            const c = self.source[start];

            switch (c) {
                // Reject raw embedded NUL bytes as invalid characters instead of misreading as EOF.
                0 => {
                    self.index += 1;
                    return .{ .tag = .invalid_char, .loc = .{ .start = start, .end = self.index } };
                },
                '(' => return self.single(.l_paren),
                ')' => return self.single(.r_paren),
                '{' => return self.single(.l_brace),
                '}' => return self.single(.r_brace),
                '[' => return self.single(.l_bracket),
                ']' => return self.single(.r_bracket),
                ',' => return self.single(.comma),
                ':' => return self.single(.colon),
                ';' => return self.single(.semicolon),
                '@' => return self.single(.at),
                '?' => return self.single(.question),
                '^' => return self.single(.caret),

                '.' => {
                    if (self.index + 2 < self.source.len and
                        self.source[self.index + 1] == '.' and
                        self.source[self.index + 2] == '=')
                    {
                        self.index += 3;
                        return .{ .tag = .dot_dot_eq, .loc = .{ .start = start, .end = self.index } };
                    }
                    if (self.index + 1 < self.source.len and self.source[self.index + 1] == '.') {
                        self.index += 2;
                        return .{ .tag = .dot_dot, .loc = .{ .start = start, .end = self.index } };
                    }
                    return self.single(.dot);
                },

                '~' => {
                    if (self.peekNext('>')) {
                        self.index += 2;
                        return .{ .tag = .tilde_arrow, .loc = .{ .start = start, .end = self.index } };
                    }
                    return self.single(.tilde);
                },

                '|' => {
                    if (self.peekNext('>')) {
                        self.index += 2;
                        return .{ .tag = .pipe, .loc = .{ .start = start, .end = self.index } };
                    }
                    if (self.peekNext('|')) {
                        self.index += 2;
                        return .{ .tag = .pipe_pipe, .loc = .{ .start = start, .end = self.index } };
                    }
                    return self.single(.bar);
                },

                '+' => {
                    if (self.peekNext('=')) return self.two(.plus_eq);
                    if (self.peekNext('%')) return self.two(.plus_percent);
                    if (self.peekNext('|')) return self.two(.plus_pipe);
                    return self.single(.plus);
                },

                '-' => {
                    if (self.peekNext('>')) return self.two(.arrow);
                    if (self.peekNext('=')) return self.two(.minus_eq);
                    if (self.peekNext('%')) return self.two(.minus_percent);
                    if (self.peekNext('|')) return self.two(.minus_pipe);
                    return self.single(.minus);
                },

                '*' => {
                    if (self.peekNext('=')) return self.two(.star_eq);
                    if (self.peekNext('%')) return self.two(.star_percent);
                    if (self.peekNext('|')) return self.two(.star_pipe);
                    return self.single(.star);
                },

                '/' => {
                    if (self.peekNext('=')) return self.two(.slash_eq);
                    if (self.peekNext('/')) {
                        if (self.lexSlashComment(start)) |tok| return tok;
                        continue;
                    }
                    return self.single(.slash);
                },

                '%' => {
                    if (self.peekNext('=')) return self.two(.percent_eq);
                    return self.single(.percent);
                },

                '=' => {
                    if (self.peekNext('=')) return self.two(.eq_eq);
                    if (self.peekNext('>')) return self.two(.fat_arrow);
                    return self.single(.eq);
                },

                '!' => {
                    if (self.peekNext('=')) return self.two(.bang_eq);
                    return self.single(.bang);
                },

                '<' => {
                    if (self.peekNext('=')) return self.two(.lt_eq);
                    if (self.peekNext('-')) return self.two(.left_arrow);
                    if (self.peekNext('<')) return self.two(.lt_lt);
                    if (self.peekNext('>')) return self.two(.lt_gt);
                    return self.single(.lt);
                },

                '>' => {
                    if (self.peekNext('=')) return self.two(.gt_eq);
                    if (self.peekNext('>')) return self.two(.gt_gt);
                    return self.single(.gt);
                },

                '&' => {
                    if (self.peekNext('&')) return self.two(.amp_amp);
                    return self.single(.amp);
                },

                '"' => return self.lexString(start),

                '0'...'9' => return self.lexNumber(start),

                '_' => return self.lexUnderscoreOrIdent(start),

                'a'...'z' => return self.lexLowerIdentOrKeyword(start),

                'A'...'Z' => return self.lexUpperIdent(start),

                else => {
                    if (c < 0x80) {
                        self.index += 1;
                        return .{ .tag = .invalid_char, .loc = .{ .start = start, .end = self.index } };
                    }
                    const rest = self.source[start..];
                    if (validUtf8Length(rest)) |seq_len| {
                        self.index += seq_len;
                        return .{ .tag = .invalid_char, .loc = .{ .start = start, .end = self.index } };
                    } else {
                        self.index += 1;
                        return .{ .tag = .invalid_utf8, .loc = .{ .start = start, .end = self.index } };
                    }
                },
            }
        }
    }

    fn single(self: *Lexer, tag: Token.Tag) Token {
        const start = self.index;
        self.index += 1;
        return .{ .tag = tag, .loc = .{ .start = start, .end = self.index } };
    }

    fn two(self: *Lexer, tag: Token.Tag) Token {
        const start = self.index;
        self.index += 2;
        return .{ .tag = tag, .loc = .{ .start = start, .end = self.index } };
    }

    fn peekNext(self: *const Lexer, expected: u8) bool {
        return self.index + 1 < self.source.len and self.source[self.index + 1] == expected;
    }

    fn skipWhitespace(self: *Lexer) void {
        while (self.index < self.source.len) {
            switch (self.source[self.index]) {
                ' ', '\t', '\r', '\n' => self.index += 1,
                else => break,
            }
        }
    }

    fn lexSlashComment(self: *Lexer, start: usize) ?Token {
        var slash_count: usize = 0;
        var i = start;
        while (i < self.source.len and self.source[i] == '/') : (i += 1) {
            slash_count += 1;
        }

        var invalid_utf8 = false;
        while (i < self.source.len) {
            const b = self.source[i];
            if (b == '\n') break;
            if (b < 0x80) {
                i += 1;
            } else if (validUtf8Length(self.source[i..])) |seq_len| {
                i += seq_len;
            } else {
                invalid_utf8 = true;
                i += 1;
            }
        }

        var token_end = i;
        if (token_end > start + slash_count and self.source[token_end - 1] == '\r') {
            token_end -= 1;
        }

        // Consume optional CRLF/LF cleanly outside token span when returning to whitespace.
        self.index = if (i < self.source.len and self.source[i] == '\n') i + 1 else i;

        if (invalid_utf8) {
            return .{ .tag = .invalid_utf8, .loc = .{ .start = start, .end = token_end } };
        }
        if (slash_count >= 4) {
            return .{ .tag = .module_doc_comment, .loc = .{ .start = start, .end = token_end } };
        }
        if (slash_count == 3) {
            return .{ .tag = .doc_comment, .loc = .{ .start = start, .end = token_end } };
        }
        return null;
    }

    fn lexUnderscoreOrIdent(self: *Lexer, start: usize) Token {
        var i = start + 1;
        while (i < self.source.len and isIdentContinue(self.source[i])) : (i += 1) {}
        self.index = i;
        if (i - start == 1) {
            return .{ .tag = .underscore, .loc = .{ .start = start, .end = i } };
        }
        return .{ .tag = .ident, .loc = .{ .start = start, .end = i } };
    }

    fn lexLowerIdentOrKeyword(self: *Lexer, start: usize) Token {
        var i = start + 1;
        while (i < self.source.len and isIdentContinue(self.source[i])) : (i += 1) {}
        self.index = i;
        const word = self.source[start..i];
        const tag = keywords.get(word) orelse .ident;
        return .{ .tag = tag, .loc = .{ .start = start, .end = i } };
    }

    fn lexUpperIdent(self: *Lexer, start: usize) Token {
        var i = start + 1;
        while (i < self.source.len and isIdentContinue(self.source[i])) : (i += 1) {}
        self.index = i;
        return .{ .tag = .upper_ident, .loc = .{ .start = start, .end = i } };
    }

    fn lexNumber(self: *Lexer, start: usize) Token {
        const len = self.source.len;
        if (self.source[start] == '0' and start + 1 < len) {
            switch (self.source[start + 1]) {
                'x', 'X' => return self.lexRadixNumber(start, 16),
                'b', 'B' => return self.lexRadixNumber(start, 2),
                'o', 'O' => return self.lexRadixNumber(start, 8),
                else => {},
            }
        }

        var i = start;
        var prev_underscore = false;
        var invalid = false;
        var is_float = false;

        // Decimal mantissa integer part
        while (i < len) {
            const b = self.source[i];
            if (b >= '0' and b <= '9') {
                prev_underscore = false;
                i += 1;
            } else if (b == '_') {
                if (prev_underscore) invalid = true;
                prev_underscore = true;
                i += 1;
            } else break;
        }

        // Fractional part ONLY when '.' is immediately followed by an ASCII digit
        // so `0..10` and `10.to_u8` remain clean tokens.
        if (i + 1 < len and self.source[i] == '.' and std.ascii.isDigit(self.source[i + 1])) {
            if (prev_underscore) invalid = true;
            is_float = true;
            i += 1;
            prev_underscore = false;
            var frac_digits: usize = 0;
            while (i < len) {
                const b = self.source[i];
                if (b >= '0' and b <= '9') {
                    frac_digits += 1;
                    prev_underscore = false;
                    i += 1;
                } else if (b == '_') {
                    if (frac_digits == 0 or prev_underscore) invalid = true;
                    prev_underscore = true;
                    i += 1;
                } else break;
            }
            if (frac_digits == 0) invalid = true;
        }

        // Optional decimal exponent (`e`/`E`)
        if (i < len and (self.source[i] == 'e' or self.source[i] == 'E')) {
            if (prev_underscore) invalid = true;
            is_float = true;
            i += 1;
            if (i < len and (self.source[i] == '+' or self.source[i] == '-')) {
                i += 1;
            }
            var exp_digits: usize = 0;
            prev_underscore = false;
            while (i < len) {
                const b = self.source[i];
                if (b >= '0' and b <= '9') {
                    exp_digits += 1;
                    prev_underscore = false;
                    i += 1;
                } else if (b == '_') {
                    if (exp_digits == 0 or prev_underscore) invalid = true;
                    prev_underscore = true;
                    i += 1;
                } else break;
            }
            if (exp_digits == 0) invalid = true;
        }

        return self.finishNumber(start, i, is_float, prev_underscore, invalid);
    }

    fn lexRadixNumber(self: *Lexer, start: usize, comptime radix: u8) Token {
        const len = self.source.len;
        var i = start + 2;
        var had_digit = false;
        var prev_underscore = false;
        var invalid = false;

        while (i < len) {
            const b = self.source[i];
            if (isRadixDigit(b, radix)) {
                had_digit = true;
                prev_underscore = false;
                i += 1;
            } else if (b == '_') {
                if (!had_digit or prev_underscore) invalid = true;
                prev_underscore = true;
                i += 1;
            } else break;
        }

        if (!had_digit) invalid = true;
        return self.finishNumber(start, i, false, prev_underscore, invalid);
    }

    fn finishNumber(
        self: *Lexer,
        start: usize,
        mantissa_end: usize,
        is_float: bool,
        trailing_underscore: bool,
        mantissa_invalid: bool,
    ) Token {
        const len = self.source.len;
        var i = mantissa_end;
        var invalid = mantissa_invalid or trailing_underscore;

        // Glued alphanumeric/underscore suffixes (e.g. `32u8`, `1.5f32`, `123abc`) are rejected
        // while still consuming the full run so error recovery stays aligned.
        if (i < len and isIdentContinue(self.source[i])) {
            while (i < len and isIdentContinue(self.source[i])) : (i += 1) {}
            invalid = true;
        }

        self.index = i;
        if (invalid) {
            return .{ .tag = .invalid_number, .loc = .{ .start = start, .end = i } };
        }
        return .{
            .tag = if (is_float) .float_literal else .int_literal,
            .loc = .{ .start = start, .end = i },
        };
    }

    fn lexString(self: *Lexer, start: usize) Token {
        const len = self.source.len;
        var i = start + 1;
        var unterminated = false;
        var invalid_escape = false;
        var invalid_utf8 = false;

        while (i < len) {
            const b = self.source[i];
            if (b == '"') {
                i += 1;
                break;
            }
            if (b == '\\') {
                i += 1;
                if (i >= len) {
                    unterminated = true;
                    break;
                }
                const esc = self.source[i];
                switch (esc) {
                    'n', 'r', 't', '\\', '"', '0' => {
                        i += 1;
                    },
                    'x' => {
                        i += 1;
                        if (i + 1 < len and isRadixDigit(self.source[i], 16) and isRadixDigit(self.source[i + 1], 16)) {
                            i += 2;
                        } else {
                            invalid_escape = true;
                        }
                    },
                    'u' => {
                        i += 1;
                        if (i >= len or self.source[i] != '{') {
                            invalid_escape = true;
                        } else {
                            i += 1; // skip '{'
                            var val: u32 = 0;
                            var digits: usize = 0;
                            var saw_non_hex = false;
                            var closed = false;
                            while (i < len) {
                                const ch = self.source[i];
                                if (ch == '}') {
                                    closed = true;
                                    i += 1;
                                    break;
                                }
                                if (ch == '"' or ch == '\n') {
                                    break;
                                }
                                if (hexVal(ch)) |hv| {
                                    if (digits < 6) {
                                        val = (val * 16) + hv;
                                    }
                                    digits += 1;
                                    i += 1;
                                } else {
                                    saw_non_hex = true;
                                    if (ch < 0x80) {
                                        i += 1;
                                    } else if (validUtf8Length(self.source[i..])) |seq_len| {
                                        i += seq_len;
                                    } else {
                                        invalid_utf8 = true;
                                        i += 1;
                                    }
                                }
                            }
                            if (!closed or saw_non_hex or digits == 0 or digits > 6 or
                                val > 0x10FFFF or (val >= 0xD800 and val <= 0xDFFF))
                            {
                                invalid_escape = true;
                            }
                        }
                    },
                    else => {
                        invalid_escape = true;
                        if (esc < 0x80) {
                            i += 1;
                        } else if (validUtf8Length(self.source[i..])) |seq_len| {
                            i += seq_len;
                        } else {
                            invalid_utf8 = true;
                            i += 1;
                        }
                    },
                }
            } else if (b < 0x80) {
                i += 1;
            } else if (validUtf8Length(self.source[i..])) |seq_len| {
                i += seq_len;
            } else {
                invalid_utf8 = true;
                i += 1;
            }
        } else {
            unterminated = true;
        }

        self.index = i;
        if (unterminated) {
            return .{ .tag = .unterminated_string, .loc = .{ .start = start, .end = i } };
        }
        if (invalid_utf8) {
            return .{ .tag = .invalid_utf8, .loc = .{ .start = start, .end = i } };
        }
        if (invalid_escape) {
            return .{ .tag = .invalid_escape, .loc = .{ .start = start, .end = i } };
        }
        return .{ .tag = .string_literal, .loc = .{ .start = start, .end = i } };
    }
};

fn isIdentContinue(b: u8) bool {
    return (b >= 'a' and b <= 'z') or (b >= 'A' and b <= 'Z') or (b >= '0' and b <= '9') or b == '_';
}

fn isRadixDigit(b: u8, comptime radix: u8) bool {
    return switch (radix) {
        2 => b == '0' or b == '1',
        8 => b >= '0' and b <= '7',
        16 => (b >= '0' and b <= '9') or (b >= 'a' and b <= 'f') or (b >= 'A' and b <= 'F'),
        else => @compileError("unsupported radix"),
    };
}

fn hexVal(b: u8) ?u32 {
    if (b >= '0' and b <= '9') return b - '0';
    if (b >= 'a' and b <= 'f') return (b - 'a') + 10;
    if (b >= 'A' and b <= 'F') return (b - 'A') + 10;
    return null;
}

fn validUtf8Length(bytes: []const u8) ?u3 {
    if (bytes.len == 0) return null;
    const seq_len = std.unicode.utf8ByteSequenceLength(bytes[0]) catch return null;
    if (bytes.len < seq_len) return null;
    _ = std.unicode.utf8Decode(bytes[0..seq_len]) catch return null;
    return seq_len;
}
