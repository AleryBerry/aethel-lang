const std = @import("std");
const lexer = @import("lexer.zig");
const ast = @import("ast.zig");

const Token = lexer.Token;
const Span = ast.Span;
const Diagnostic = ast.Diagnostic;

pub const max_nesting_depth: u16 = 256;

/// Parse an Aethel source buffer into an arena-owned `ast.Ast` with structured
/// lexer and parser diagnostics and guaranteed forward progress on malformed input.
pub fn parse(allocator: std.mem.Allocator, source: [:0]const u8) std.mem.Allocator.Error!ast.Ast {
    var arena = std.heap.ArenaAllocator.init(allocator);
    errdefer arena.deinit();
    const alloc = arena.allocator();

    var raw_tokens: std.ArrayList(Token) = .empty;
    var clean_tokens: std.ArrayList(Token) = .empty;
    var diagnostics: std.ArrayList(Diagnostic) = .empty;

    var lex = lexer.Lexer.init(source);
    while (true) {
        const tok = lex.next();
        try raw_tokens.append(alloc, tok);
        if (tok.tag.isError()) {
            try diagnostics.append(alloc, .{
                .span = Span.fromLoc(tok.loc),
                .kind = .lexer_error,
                .message = lexerErrorMessage(tok.tag),
            });
        } else {
            try clean_tokens.append(alloc, tok);
        }
        if (tok.tag == .eof) break;
    }

    var parser = Parser{
        .alloc = alloc,
        .source = source,
        .tokens = try clean_tokens.toOwnedSlice(alloc),
        .cursor = 0,
        .depth = 0,
        .diagnostics = &diagnostics,
    };

    const module = try parser.parseModule();

    return .{
        .arena = arena,
        .source = source,
        .tokens = try raw_tokens.toOwnedSlice(alloc),
        .module = module,
        .diagnostics = try diagnostics.toOwnedSlice(alloc),
    };
}

fn lexerErrorMessage(tag: Token.Tag) []const u8 {
    return switch (tag) {
        .invalid_char => "invalid character in source",
        .invalid_utf8 => "invalid UTF-8 byte sequence",
        .invalid_number => "malformed numeric literal or width suffix",
        .unterminated_string => "unterminated string literal",
        .invalid_escape => "invalid string escape sequence",
        else => "lexer error",
    };
}

const Parser = struct {
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    tokens: []const Token,
    cursor: usize,
    depth: u16,
    diagnostics: *std.ArrayList(Diagnostic),

    fn eofToken(self: *const Parser) Token {
        return self.tokens[self.tokens.len - 1];
    }

    fn peekOffset(self: *const Parser, offset: usize) Token {
        var idx = self.cursor;
        var seen: usize = 0;
        while (idx < self.tokens.len) : (idx += 1) {
            const tok = self.tokens[idx];
            if (tok.tag == .doc_comment or tok.tag == .module_doc_comment) continue;
            if (seen == offset) return tok;
            seen += 1;
        }
        return self.eofToken();
    }

    fn peek(self: *const Parser) Token {
        return self.peekOffset(0);
    }

    fn peek2(self: *const Parser) Token {
        return self.peekOffset(1);
    }

    fn at(self: *const Parser, tag: Token.Tag) bool {
        return self.peek().tag == tag;
    }

    fn atContextual(self: *const Parser, kw: lexer.ContextualKeyword) bool {
        const tok = self.peek();
        if (tok.tag != .ident) return false;
        return lexer.contextualKeyword(tok.loc.slice(self.source)) == kw;
    }

    fn skipDocTrivia(self: *Parser) void {
        while (self.cursor < self.tokens.len) {
            const tag = self.tokens[self.cursor].tag;
            if (tag != .doc_comment and tag != .module_doc_comment) break;
            self.cursor += 1;
        }
    }

    fn advance(self: *Parser) Token {
        self.skipDocTrivia();
        const tok = self.tokens[self.cursor];
        if (tok.tag != .eof) {
            self.cursor += 1;
        }
        return tok;
    }

    fn match(self: *Parser, tag: Token.Tag) ?Token {
        if (self.at(tag)) {
            return self.advance();
        }
        return null;
    }

    fn reportError(self: *Parser, kind: Diagnostic.Kind, span: Span, message: []const u8) void {
        self.diagnostics.append(self.alloc, .{
            .span = span,
            .kind = kind,
            .message = message,
        }) catch {};
    }

    fn expect(self: *Parser, tag: Token.Tag, message: []const u8) ?Token {
        if (self.at(tag)) {
            return self.advance();
        }
        const tok = self.peek();
        self.reportError(.expected_token, Span.fromLoc(tok.loc), message);
        return null;
    }

    fn enterDepth(self: *Parser, span: Span) bool {
        if (self.depth >= max_nesting_depth) {
            self.reportError(.nesting_depth_exceeded, span, "maximum syntax nesting depth exceeded");
            return false;
        }
        self.depth += 1;
        return true;
    }

    fn leaveDepth(self: *Parser) void {
        self.depth -= 1;
    }

    fn collectModuleDocs(self: *Parser) std.mem.Allocator.Error![]const Span {
        var docs: std.ArrayList(Span) = .empty;
        while (self.cursor < self.tokens.len and self.tokens[self.cursor].tag == .module_doc_comment) {
            try docs.append(self.alloc, Span.fromLoc(self.tokens[self.cursor].loc));
            self.cursor += 1;
        }
        return try docs.toOwnedSlice(self.alloc);
    }

    fn collectDocComments(self: *Parser) std.mem.Allocator.Error![]const Span {
        var docs: std.ArrayList(Span) = .empty;
        while (self.cursor < self.tokens.len) {
            const tok = self.tokens[self.cursor];
            if (tok.tag == .doc_comment) {
                try docs.append(self.alloc, Span.fromLoc(tok.loc));
                self.cursor += 1;
            } else if (tok.tag == .module_doc_comment) {
                self.cursor += 1;
            } else {
                break;
            }
        }
        return try docs.toOwnedSlice(self.alloc);
    }

    fn makeErrExpr(self: *Parser, span: Span) std.mem.Allocator.Error!*const ast.Expr {
        const ptr = try self.alloc.create(ast.Expr);
        ptr.* = .{ .err = span };
        return ptr;
    }

    fn allocExpr(self: *Parser, expr: ast.Expr) std.mem.Allocator.Error!*const ast.Expr {
        const ptr = try self.alloc.create(ast.Expr);
        ptr.* = expr;
        return ptr;
    }

    fn allocType(self: *Parser, ty: ast.TypeExpr) std.mem.Allocator.Error!*const ast.TypeExpr {
        const ptr = try self.alloc.create(ast.TypeExpr);
        ptr.* = ty;
        return ptr;
    }

    fn allocPattern(self: *Parser, pat: ast.Pattern) std.mem.Allocator.Error!*const ast.Pattern {
        const ptr = try self.alloc.create(ast.Pattern);
        ptr.* = pat;
        return ptr;
    }

    fn synchronizeDecl(self: *Parser) void {
        while (!self.at(.eof)) {
            if (isDeclStart(self.peek().tag)) return;
            if (self.peek().tag == .r_brace) {
                _ = self.advance();
                return;
            }
            _ = self.advance();
        }
    }

    fn isDeclStart(tag: Token.Tag) bool {
        return switch (tag) {
            .kw_pub, .kw_import, .kw_type, .kw_opaque, .kw_fn, .kw_const, .kw_law, .kw_extern, .at => true,
            else => false,
        };
    }

    fn parseModule(self: *Parser) std.mem.Allocator.Error!ast.Module {
        const mod_docs = try self.collectModuleDocs();
        var decls: std.ArrayList(ast.Decl) = .empty;

        while (!self.at(.eof)) {
            const loop_cursor = self.cursor;
            if (try self.parseDecl()) |decl| {
                try decls.append(self.alloc, decl);
            } else {
                self.synchronizeDecl();
            }
            if (self.cursor == loop_cursor and !self.at(.eof)) {
                _ = self.advance();
            }
        }

        return .{
            .doc_comments = mod_docs,
            .decls = try decls.toOwnedSlice(self.alloc),
        };
    }

    fn parseAttributes(self: *Parser) std.mem.Allocator.Error![]const ast.Attribute {
        var attrs: std.ArrayList(ast.Attribute) = .empty;
        while (self.match(.at)) |at_tok| {
            const name_tok = if (self.at(.ident) or self.at(.upper_ident))
                self.advance()
            else blk: {
                self.reportError(.invalid_attribute, Span.fromLoc(at_tok.loc), "expected attribute name after '@'");
                break :blk Token{ .tag = .ident, .loc = at_tok.loc };
            };
            const name_span = Span.fromLoc(name_tok.loc);
            var end_span = name_span;
            var payload: ast.Attribute.Payload = .none;

            if (self.match(.l_paren)) |_| {
                if (std.mem.eql(u8, name_span.slice(self.source), "layout")) {
                    const spec = try self.parseLayoutSpec();
                    const close = self.expect(.r_paren, "expected ')' after @layout specification");
                    end_span = if (close) |c| Span.fromLoc(c.loc) else Span.fromLoc(self.peek().loc);
                    payload = .{ .layout = spec };
                } else {
                    var args: std.ArrayList(*const ast.Expr) = .empty;
                    while (!self.at(.r_paren) and !self.at(.eof)) {
                        const iter_start = self.cursor;
                        const arg = try self.parseExprPrec(1, true);
                        try args.append(self.alloc, arg);
                        if (self.match(.comma) == null) break;
                        if (self.cursor == iter_start) break;
                    }
                    const close = self.expect(.r_paren, "expected ')' after attribute arguments");
                    end_span = if (close) |c| Span.fromLoc(c.loc) else Span.fromLoc(self.peek().loc);
                    payload = .{ .args = try args.toOwnedSlice(self.alloc) };
                }
            }

            try attrs.append(self.alloc, .{
                .span = Span.merge(Span.fromLoc(at_tok.loc), end_span),
                .name = name_span,
                .payload = payload,
            });
        }
        return try attrs.toOwnedSlice(self.alloc);
    }

    fn parseLayoutSpec(self: *Parser) std.mem.Allocator.Error!ast.LayoutSpec {
        const tok = self.peek();
        if (tok.tag != .ident) {
            self.reportError(.invalid_attribute, Span.fromLoc(tok.loc), "expected layout policy ('aos', 'soa', 'aosoa', or 'packed')");
            return .aos;
        }
        const kw = lexer.contextualKeyword(tok.loc.slice(self.source));
        _ = self.advance();
        return switch (kw orelse .layout) {
            .aos => .aos,
            .soa => .soa,
            .@"packed" => .@"packed",
            .aosoa => blk: {
                var tile: ?*const ast.Expr = null;
                if (self.match(.l_paren)) |_| {
                    if (!self.at(.r_paren)) {
                        tile = try self.parseExprPrec(1, true);
                    }
                    _ = self.expect(.r_paren, "expected ')' after aosoa tile width");
                }
                break :blk .{ .aosoa = tile };
            },
            else => {
                self.reportError(.invalid_attribute, Span.fromLoc(tok.loc), "unknown layout policy in @layout(...)");
                return .aos;
            },
        };
    }

    fn parseDecl(self: *Parser) std.mem.Allocator.Error!?ast.Decl {
        const docs = try self.collectDocComments();
        const attrs = try self.parseAttributes();
        const start_tok = self.peek();
        if (!self.enterDepth(Span.fromLoc(start_tok.loc))) {
            if (!self.at(.eof)) _ = self.advance();
            return null;
        }
        defer self.leaveDepth();

        const pub_tok = self.match(.kw_pub);
        const start_span = if (attrs.len > 0)
            attrs[0].span
        else if (pub_tok) |pt|
            Span.fromLoc(pt.loc)
        else
            Span.fromLoc(self.peek().loc);

        const is_pub = pub_tok != null;
        const head = self.peek();

        switch (head.tag) {
            .kw_import => {
                const kind = try self.parseImportDecl();
                return ast.Decl{
                    .span = Span.merge(start_span, self.lastConsumedSpan(head)),
                    .doc_comments = docs,
                    .attrs = attrs,
                    .is_pub = is_pub,
                    .kind = kind,
                };
            },
            .kw_opaque, .kw_type => {
                const kind = try self.parseTypeDecl();
                return ast.Decl{
                    .span = Span.merge(start_span, self.lastConsumedSpan(head)),
                    .doc_comments = docs,
                    .attrs = attrs,
                    .is_pub = is_pub,
                    .kind = kind,
                };
            },
            .kw_fn => {
                const kind = try self.parseFnDecl();
                return ast.Decl{
                    .span = Span.merge(start_span, self.lastConsumedSpan(head)),
                    .doc_comments = docs,
                    .attrs = attrs,
                    .is_pub = is_pub,
                    .kind = kind,
                };
            },
            .kw_const => {
                const kind = try self.parseConstDecl();
                return ast.Decl{
                    .span = Span.merge(start_span, self.lastConsumedSpan(head)),
                    .doc_comments = docs,
                    .attrs = attrs,
                    .is_pub = is_pub,
                    .kind = kind,
                };
            },
            .kw_law => {
                const kind = try self.parseLawDecl();
                return ast.Decl{
                    .span = Span.merge(start_span, self.lastConsumedSpan(head)),
                    .doc_comments = docs,
                    .attrs = attrs,
                    .is_pub = is_pub,
                    .kind = kind,
                };
            },
            .kw_extern => {
                const kind = try self.parseExternDecl();
                return ast.Decl{
                    .span = Span.merge(start_span, self.lastConsumedSpan(head)),
                    .doc_comments = docs,
                    .attrs = attrs,
                    .is_pub = is_pub,
                    .kind = kind,
                };
            },
            else => {
                self.reportError(.expected_decl, Span.fromLoc(head.loc), "expected top-level declaration ('import', 'type', 'opaque', 'fn', 'const', 'law', or 'extern')");
                return null;
            },
        }
    }

    fn lastConsumedSpan(self: *const Parser, fallback: Token) Span {
        if (self.cursor == 0) return Span.fromLoc(fallback.loc);
        return Span.fromLoc(self.tokens[self.cursor - 1].loc);
    }

    fn parseAnyIdentSpan(self: *Parser, message: []const u8) Span {
        const tok = self.peek();
        if (tok.tag == .ident or tok.tag == .upper_ident) {
            _ = self.advance();
            return Span.fromLoc(tok.loc);
        }
        self.reportError(.expected_token, Span.fromLoc(tok.loc), message);
        return Span.fromLoc(tok.loc);
    }

    fn parseImportDecl(self: *Parser) std.mem.Allocator.Error!ast.Decl.Kind {
        _ = self.advance(); // consume 'import'
        var path: std.ArrayList(Span) = .empty;
        var members: std.ArrayList(Span) = .empty;
        var alias: ?Span = null;

        try path.append(self.alloc, self.parseAnyIdentSpan("expected module path after 'import'"));

        while (self.at(.slash) or self.at(.dot)) {
            const sep = self.advance();
            if (sep.tag == .dot and self.match(.l_brace) != null) {
                while (!self.at(.r_brace) and !self.at(.eof)) {
                    const iter_start = self.cursor;
                    try members.append(self.alloc, self.parseAnyIdentSpan("expected imported symbol name"));
                    if (self.match(.comma) == null) break;
                    if (self.cursor == iter_start) break;
                }
                _ = self.expect(.r_brace, "expected '}' after import member list");
                break;
            }
            try path.append(self.alloc, self.parseAnyIdentSpan("expected module path segment"));
        }

        if (self.match(.kw_as) != null) {
            alias = self.parseAnyIdentSpan("expected module alias after 'as'");
        }

        return .{ .import_decl = .{
            .path = try path.toOwnedSlice(self.alloc),
            .alias = alias,
            .members = try members.toOwnedSlice(self.alloc),
        } };
    }

    fn parseTypeDecl(self: *Parser) std.mem.Allocator.Error!ast.Decl.Kind {
        var is_opaque = false;
        if (self.match(.kw_opaque) != null) {
            is_opaque = true;
        }
        _ = self.expect(.kw_type, "expected 'type'");

        const name = self.parseAnyIdentSpan("expected type name");

        var type_params: std.ArrayList(Span) = .empty;
        if (self.match(.l_paren) != null) {
            while (!self.at(.r_paren) and !self.at(.eof)) {
                const iter_start = self.cursor;
                try type_params.append(self.alloc, self.parseAnyIdentSpan("expected type parameter name"));
                if (self.match(.comma) == null) break;
                if (self.cursor == iter_start) break;
            }
            _ = self.expect(.r_paren, "expected ')' after type parameters");
        }

        var body: ast.TypeBody = .empty;
        if (self.match(.eq) != null) {
            body = .{ .alias = try self.parseType() };
        } else if (self.match(.l_brace) != null) {
            body = try self.parseTypeBody();
        }

        return .{ .type_decl = .{
            .is_opaque = is_opaque,
            .name = name,
            .type_params = try type_params.toOwnedSlice(self.alloc),
            .body = body,
        } };
    }

    fn parseTypeBody(self: *Parser) std.mem.Allocator.Error!ast.TypeBody {
        if (self.at(.r_brace)) {
            _ = self.advance();
            return .{ .record = &.{} };
        }

        const is_record = self.looksLikeRecordBody();
        if (is_record) {
            var fields: std.ArrayList(ast.RecordField) = .empty;
            while (!self.at(.r_brace) and !self.at(.eof)) {
                const iter_start = self.cursor;
                const f_docs = try self.collectDocComments();
                const f_attrs = try self.parseAttributes();
                const f_pub = self.match(.kw_pub);
                const f_mut = self.match(.kw_mut);
                const name_tok = self.peek();
                const f_name = self.parseAnyIdentSpan("expected record field name");
                _ = self.expect(.colon, "expected ':' after record field name");
                const f_ty = try self.parseType();
                const f_start = if (f_attrs.len > 0)
                    f_attrs[0].span
                else if (f_pub) |p|
                    Span.fromLoc(p.loc)
                else if (f_mut) |m|
                    Span.fromLoc(m.loc)
                else
                    Span.fromLoc(name_tok.loc);
                try fields.append(self.alloc, .{
                    .span = Span.merge(f_start, f_ty.getSpan()),
                    .doc_comments = f_docs,
                    .attrs = f_attrs,
                    .is_pub = f_pub != null,
                    .mutable = f_mut != null,
                    .name = f_name,
                    .ty = f_ty,
                });
                _ = self.match(.comma);
                if (self.cursor == iter_start and !self.at(.eof)) _ = self.advance();
            }
            _ = self.expect(.r_brace, "expected '}' closing record type fields");
            return .{ .record = try fields.toOwnedSlice(self.alloc) };
        }

        var variants: std.ArrayList(ast.Variant) = .empty;
        while (!self.at(.r_brace) and !self.at(.eof)) {
            const iter_start = self.cursor;
            const v_docs = try self.collectDocComments();
            const v_attrs = try self.parseAttributes();
            _ = self.match(.bar);
            const v_tok = self.peek();
            const v_name = self.parseAnyIdentSpan("expected variant constructor name");
            var v_end = v_name;
            var v_fields: std.ArrayList(ast.VariantField) = .empty;

            if (self.match(.l_paren) != null) {
                while (!self.at(.r_paren) and !self.at(.eof)) {
                    const vf_start = self.cursor;
                    const first = self.peek();
                    const second = self.peek2();
                    var label: ?Span = null;
                    if (first.tag == .ident and second.tag == .colon) {
                        label = Span.fromLoc(self.advance().loc);
                        _ = self.advance(); // ':'
                    }
                    const is_mut = self.match(.kw_mut) != null;
                    const ty = try self.parseType();
                    try v_fields.append(self.alloc, .{
                        .span = Span.merge(label orelse Span.fromLoc(first.loc), ty.getSpan()),
                        .label = label,
                        .mutable = is_mut,
                        .ty = ty,
                    });
                    if (self.match(.comma) == null) break;
                    if (self.cursor == vf_start) break;
                }
                const close = self.expect(.r_paren, "expected ')' after variant payload fields");
                if (close) |c| v_end = Span.fromLoc(c.loc);
            }

            const v_start = if (v_attrs.len > 0) v_attrs[0].span else Span.fromLoc(v_tok.loc);
            try variants.append(self.alloc, .{
                .span = Span.merge(v_start, v_end),
                .doc_comments = v_docs,
                .attrs = v_attrs,
                .name = v_name,
                .fields = try v_fields.toOwnedSlice(self.alloc),
            });
            _ = self.match(.comma);
            if (self.cursor == iter_start and !self.at(.eof)) _ = self.advance();
        }
        _ = self.expect(.r_brace, "expected '}' closing ADT variants");
        return .{ .variants = try variants.toOwnedSlice(self.alloc) };
    }

    fn looksLikeRecordBody(self: *const Parser) bool {
        var idx = self.cursor;
        // Skip optional leading doc comments / attributes before deciding.
        while (idx < self.tokens.len) {
            const tag = self.tokens[idx].tag;
            if (tag == .doc_comment or tag == .module_doc_comment) {
                idx += 1;
                continue;
            }
            if (tag == .at) {
                idx += 1;
                if (idx < self.tokens.len and (self.tokens[idx].tag == .ident or self.tokens[idx].tag == .upper_ident)) {
                    idx += 1;
                }
                if (idx < self.tokens.len and self.tokens[idx].tag == .l_paren) {
                    var paren_depth: usize = 1;
                    idx += 1;
                    while (idx < self.tokens.len and paren_depth > 0) : (idx += 1) {
                        if (self.tokens[idx].tag == .l_paren) paren_depth += 1 else if (self.tokens[idx].tag == .r_paren) paren_depth -= 1;
                    }
                }
                continue;
            }
            return tag == .kw_pub or tag == .kw_mut or tag == .ident;
        }
        return false;
    }

    fn parseFnDecl(self: *Parser) std.mem.Allocator.Error!ast.Decl.Kind {
        _ = self.advance(); // 'fn'
        const name = self.parseAnyIdentSpan("expected function name");
        const params = try self.parseParamList(true);
        var ret: ?*const ast.TypeExpr = null;
        if (self.match(.arrow) != null) {
            ret = try self.parseType();
        }
        var decreases: ?*const ast.Expr = null;
        if (self.atContextual(.decreases)) {
            _ = self.advance();
            decreases = try self.parseExprPrec(1, false);
        }
        const body = try self.parseBlock();
        return .{ .fn_decl = .{
            .name = name,
            .params = params,
            .ret = ret,
            .decreases = decreases,
            .body = body,
        } };
    }

    fn parseParamList(self: *Parser, require_types: bool) std.mem.Allocator.Error![]const ast.Param {
        _ = self.expect(.l_paren, "expected '(' starting parameter list");
        var params: std.ArrayList(ast.Param) = .empty;
        while (!self.at(.r_paren) and !self.at(.eof)) {
            const iter_start = self.cursor;
            const first = self.peek();
            var label: ?Span = null;
            var is_mut = false;
            var name: Span = undefined;

            if (first.tag == .kw_mut) {
                is_mut = true;
                _ = self.advance();
                name = self.parseAnyIdentSpan("expected parameter name after 'mut'");
            } else if ((first.tag == .ident or first.tag == .underscore) and
                (self.peek2().tag == .ident or self.peek2().tag == .kw_mut))
            {
                label = Span.fromLoc(self.advance().loc);
                is_mut = self.match(.kw_mut) != null;
                name = self.parseAnyIdentSpan("expected parameter name after label");
            } else {
                const tok = self.peek();
                if (tok.tag == .ident or tok.tag == .underscore or tok.tag == .upper_ident) {
                    name = Span.fromLoc(self.advance().loc);
                } else {
                    self.reportError(.expected_token, Span.fromLoc(tok.loc), "expected parameter name");
                    name = Span.fromLoc(tok.loc);
                }
            }

            var ty: ?*const ast.TypeExpr = null;
            var end_span = name;
            if (self.match(.colon) != null) {
                const parsed_ty = try self.parseType();
                ty = parsed_ty;
                end_span = parsed_ty.getSpan();
            } else if (require_types) {
                const tok = self.peek();
                self.reportError(.expected_type, Span.fromLoc(tok.loc), "expected ': Type' annotation for parameter");
            }

            try params.append(self.alloc, .{
                .span = Span.merge(label orelse Span.fromLoc(first.loc), end_span),
                .label = label,
                .mutable = is_mut,
                .name = name,
                .ty = ty,
            });

            if (self.match(.comma) == null) break;
            if (self.cursor == iter_start) break;
        }
        _ = self.expect(.r_paren, "expected ')' after parameter list");
        return try params.toOwnedSlice(self.alloc);
    }

    fn parseConstDecl(self: *Parser) std.mem.Allocator.Error!ast.Decl.Kind {
        _ = self.advance(); // 'const'
        const name = self.parseAnyIdentSpan("expected constant name");
        var ty: ?*const ast.TypeExpr = null;
        if (self.match(.colon) != null) {
            ty = try self.parseType();
        }
        _ = self.expect(.eq, "expected '=' in const declaration");
        const value = try self.parseExprPrec(1, true);
        _ = self.match(.semicolon);
        return .{ .const_decl = .{
            .name = name,
            .ty = ty,
            .value = value,
        } };
    }

    fn parseLawDecl(self: *Parser) std.mem.Allocator.Error!ast.Decl.Kind {
        _ = self.advance(); // 'law'
        const name = self.parseAnyIdentSpan("expected law name");
        const params = try self.parseParamList(true);
        _ = self.expect(.l_brace, "expected '{' before law clauses");

        var clauses: std.ArrayList(ast.LawClause) = .empty;
        while (!self.at(.r_brace) and !self.at(.eof)) {
            const iter_start = self.cursor;
            if (self.atContextual(.preserves)) {
                const kw_tok = self.advance();
                var paths: std.ArrayList(ast.FieldPath) = .empty;
                var end_span = Span.fromLoc(kw_tok.loc);
                while (!self.at(.r_brace) and !self.at(.eof)) {
                    const p = try self.parseFieldPath();
                    if (p.len > 0) end_span = p[p.len - 1];
                    try paths.append(self.alloc, p);
                    if (self.match(.comma) == null) break;
                }
                try clauses.append(self.alloc, .{ .preserves = .{
                    .span = Span.merge(Span.fromLoc(kw_tok.loc), end_span),
                    .paths = try paths.toOwnedSlice(self.alloc),
                } });
            } else if (self.atContextual(.when)) {
                const kw_tok = self.advance();
                const expr = try self.parseExprPrec(1, true);
                try clauses.append(self.alloc, .{ .when = .{
                    .span = Span.merge(Span.fromLoc(kw_tok.loc), expr.getSpan()),
                    .expr = expr,
                } });
            } else if (self.atContextual(.always)) {
                const kw_tok = self.advance();
                const expr = try self.parseExprPrec(1, true);
                try clauses.append(self.alloc, .{ .always = .{
                    .span = Span.merge(Span.fromLoc(kw_tok.loc), expr.getSpan()),
                    .expr = expr,
                } });
            } else if (self.atContextual(.never)) {
                const kw_tok = self.advance();
                const expr = try self.parseExprPrec(1, true);
                try clauses.append(self.alloc, .{ .never = .{
                    .span = Span.merge(Span.fromLoc(kw_tok.loc), expr.getSpan()),
                    .expr = expr,
                } });
            } else {
                const expr = try self.parseExprPrec(1, true);
                try clauses.append(self.alloc, .{ .expr = .{
                    .span = expr.getSpan(),
                    .expr = expr,
                } });
            }
            _ = self.match(.semicolon);
            if (self.cursor == iter_start and !self.at(.eof)) {
                const bad = self.advance();
                self.reportError(.invalid_law_clause, Span.fromLoc(bad.loc), "unexpected token inside law block");
            }
        }
        _ = self.expect(.r_brace, "expected '}' closing law block");

        return .{ .law_decl = .{
            .name = name,
            .params = params,
            .clauses = try clauses.toOwnedSlice(self.alloc),
        } };
    }

    fn parseExternDecl(self: *Parser) std.mem.Allocator.Error!ast.Decl.Kind {
        _ = self.advance(); // 'extern'
        const abi_tok = self.peek();
        const abi_span = Span.fromLoc(abi_tok.loc);
        if (abi_tok.tag == .string_literal) {
            _ = self.advance();
        } else {
            self.reportError(.invalid_extern_abi, abi_span, "expected ABI string literal such as \"rust\" or \"C\" after 'extern'");
        }

        var fns: std.ArrayList(ast.ExternFn) = .empty;
        if (self.match(.l_brace) != null) {
            while (!self.at(.r_brace) and !self.at(.eof)) {
                const iter_start = self.cursor;
                if (try self.parseExternFn(abi_tok)) |ef| {
                    try fns.append(self.alloc, ef);
                } else {
                    if (!self.at(.r_brace) and !self.at(.eof)) _ = self.advance();
                }
                _ = self.match(.semicolon);
                if (self.cursor == iter_start and !self.at(.eof)) _ = self.advance();
            }
            _ = self.expect(.r_brace, "expected '}' closing extern block");
        } else {
            if (try self.parseExternFn(abi_tok)) |ef| {
                try fns.append(self.alloc, ef);
            }
            _ = self.match(.semicolon);
        }

        return .{ .extern_decl = .{
            .abi = abi_span,
            .fns = try fns.toOwnedSlice(self.alloc),
        } };
    }

    fn parseExternFn(self: *Parser, fallback: Token) std.mem.Allocator.Error!?ast.ExternFn {
        const docs = try self.collectDocComments();
        const attrs = try self.parseAttributes();
        const pub_tok = self.match(.kw_pub);
        if (self.expect(.kw_fn, "expected 'fn' in extern declaration") == null) {
            return null;
        }
        const name = self.parseAnyIdentSpan("expected extern function name");
        const params = try self.parseParamList(true);
        var ret: ?*const ast.TypeExpr = null;
        if (self.match(.arrow) != null) {
            ret = try self.parseType();
        }
        const start_span = if (attrs.len > 0)
            attrs[0].span
        else if (pub_tok) |p|
            Span.fromLoc(p.loc)
        else
            Span.fromLoc(fallback.loc);
        const end_span = if (ret) |r| r.getSpan() else self.lastConsumedSpan(fallback);
        return ast.ExternFn{
            .span = Span.merge(start_span, end_span),
            .doc_comments = docs,
            .attrs = attrs,
            .is_pub = pub_tok != null,
            .name = name,
            .params = params,
            .ret = ret,
        };
    }

    fn parseFieldPath(self: *Parser) std.mem.Allocator.Error!ast.FieldPath {
        var segs: std.ArrayList(Span) = .empty;
        const first = self.peek();
        if (first.tag == .ident or first.tag == .upper_ident or first.tag == .int_literal) {
            _ = self.advance();
            try segs.append(self.alloc, Span.fromLoc(first.loc));
        } else {
            self.reportError(.expected_token, Span.fromLoc(first.loc), "expected field path segment");
            return try segs.toOwnedSlice(self.alloc);
        }
        while (self.match(.dot) != null) {
            const seg = self.peek();
            if (seg.tag == .ident or seg.tag == .upper_ident or seg.tag == .int_literal) {
                _ = self.advance();
                try segs.append(self.alloc, Span.fromLoc(seg.loc));
            } else {
                self.reportError(.expected_token, Span.fromLoc(seg.loc), "expected field segment after '.'");
                break;
            }
        }
        return try segs.toOwnedSlice(self.alloc);
    }

    fn parseType(self: *Parser) std.mem.Allocator.Error!*const ast.TypeExpr {
        const start_tok = self.peek();
        const start_span = Span.fromLoc(start_tok.loc);
        if (!self.enterDepth(start_span)) {
            return try self.allocType(.{ .inferred = start_span });
        }
        defer self.leaveDepth();

        var base = try self.parseBaseType();

        // Handle path-scoped borrow types (`Base ~>.{pos, vel}` or `Base ~> exclusive .pos`).
        while (self.match(.tilde_arrow)) |arrow_tok| {
            var mode: ?ast.BorrowMode = null;
            if (self.atContextual(.shared)) {
                _ = self.advance();
                mode = .shared;
            } else if (self.atContextual(.exclusive)) {
                _ = self.advance();
                mode = .exclusive;
            } else if (self.match(.kw_mut) != null) {
                mode = .exclusive;
            }

            _ = self.expect(.dot, "expected '.' after '~>' borrow target");
            var paths: std.ArrayList(ast.FieldPath) = .empty;
            var end_span = Span.fromLoc(arrow_tok.loc);

            if (self.match(.l_brace) != null) {
                while (!self.at(.r_brace) and !self.at(.eof)) {
                    const iter_start = self.cursor;
                    try paths.append(self.alloc, try self.parseFieldPath());
                    if (self.match(.comma) == null) break;
                    if (self.cursor == iter_start) break;
                }
                const close = self.expect(.r_brace, "expected '}' closing path borrow list");
                end_span = if (close) |c| Span.fromLoc(c.loc) else self.lastConsumedSpan(arrow_tok);
            } else {
                const p = try self.parseFieldPath();
                if (p.len > 0) end_span = p[p.len - 1];
                try paths.append(self.alloc, p);
            }

            base = try self.allocType(.{ .path_borrow = .{
                .span = Span.merge(base.getSpan(), end_span),
                .base = base,
                .borrow = .{
                    .span = Span.merge(Span.fromLoc(arrow_tok.loc), end_span),
                    .mode = mode,
                    .paths = try paths.toOwnedSlice(self.alloc),
                },
            } });
        }

        return base;
    }

    fn parseBaseType(self: *Parser) std.mem.Allocator.Error!*const ast.TypeExpr {
        const tok = self.peek();
        switch (tok.tag) {
            .underscore => {
                _ = self.advance();
                return try self.allocType(.{ .inferred = Span.fromLoc(tok.loc) });
            },
            .kw_fn => {
                _ = self.advance();
                _ = self.expect(.l_paren, "expected '(' in fn(...) type");
                var params: std.ArrayList(*const ast.TypeExpr) = .empty;
                while (!self.at(.r_paren) and !self.at(.eof)) {
                    const iter_start = self.cursor;
                    try params.append(self.alloc, try self.parseType());
                    if (self.match(.comma) == null) break;
                    if (self.cursor == iter_start) break;
                }
                _ = self.expect(.r_paren, "expected ')' after fn parameter types");
                _ = self.expect(.arrow, "expected '->' in fn type signature");
                const ret = try self.parseType();
                return try self.allocType(.{ .fn_type = .{
                    .span = Span.merge(Span.fromLoc(tok.loc), ret.getSpan()),
                    .params = try params.toOwnedSlice(self.alloc),
                    .ret = ret,
                } });
            },
            .l_bracket => {
                _ = self.advance();
                const is_mut = self.match(.kw_mut) != null;
                const elem = try self.parseType();
                const close = self.expect(.r_bracket, "expected ']' closing slice type");
                return try self.allocType(.{ .slice = .{
                    .span = Span.merge(Span.fromLoc(tok.loc), if (close) |c| Span.fromLoc(c.loc) else elem.getSpan()),
                    .mutable = is_mut,
                    .elem = elem,
                } });
            },
            .l_paren => {
                _ = self.advance();
                if (self.match(.r_paren)) |close| {
                    return try self.allocType(.{ .tuple = .{
                        .span = Span.merge(Span.fromLoc(tok.loc), Span.fromLoc(close.loc)),
                        .elems = &.{},
                    } });
                }
                const first = try self.parseType();
                if (self.match(.comma) == null) {
                    _ = self.expect(.r_paren, "expected ')' closing parenthesized type");
                    return first;
                }
                var elems: std.ArrayList(*const ast.TypeExpr) = .empty;
                try elems.append(self.alloc, first);
                while (!self.at(.r_paren) and !self.at(.eof)) {
                    const iter_start = self.cursor;
                    try elems.append(self.alloc, try self.parseType());
                    if (self.match(.comma) == null) break;
                    if (self.cursor == iter_start) break;
                }
                const close = self.expect(.r_paren, "expected ')' closing tuple type");
                return try self.allocType(.{ .tuple = .{
                    .span = Span.merge(Span.fromLoc(tok.loc), if (close) |c| Span.fromLoc(c.loc) else elems.items[elems.items.len - 1].getSpan()),
                    .elems = try elems.toOwnedSlice(self.alloc),
                } });
            },
            .ident => {
                const slice = tok.loc.slice(self.source);
                if (self.peek2().tag != .dot and self.peek2().tag != .l_paren) {
                    if (lexer.parsePrimitiveType(slice)) |prim| {
                        _ = self.advance();
                        return try self.allocType(.{ .primitive = .{
                            .span = Span.fromLoc(tok.loc),
                            .prim = prim,
                        } });
                    }
                    _ = self.advance();
                    return try self.allocType(.{ .type_var = .{
                        .span = Span.fromLoc(tok.loc),
                        .name = Span.fromLoc(tok.loc),
                    } });
                }
                return try self.parseNamedType();
            },
            .upper_ident => {
                const slice = tok.loc.slice(self.source);
                if (std.mem.eql(u8, slice, "Int") and self.peek2().tag == .l_paren) {
                    return try self.parseIntRangeType();
                }
                return try self.parseNamedType();
            },
            else => {
                self.reportError(.expected_type, Span.fromLoc(tok.loc), "expected type expression");
                if (!self.at(.eof)) _ = self.advance();
                return try self.allocType(.{ .inferred = Span.fromLoc(tok.loc) });
            },
        }
    }

    fn parseIntRangeType(self: *Parser) std.mem.Allocator.Error!*const ast.TypeExpr {
        const kw_tok = self.advance(); // 'Int'
        _ = self.advance(); // '('
        const range_expr = try self.parseExprPrec(1, true);
        const close = self.expect(.r_paren, "expected ')' after integer range bounds");
        const full_span = Span.merge(Span.fromLoc(kw_tok.loc), if (close) |c| Span.fromLoc(c.loc) else range_expr.getSpan());

        if (range_expr.* == .binary and (range_expr.binary.op == .range or range_expr.binary.op == .range_eq)) {
            return try self.allocType(.{ .int_range = .{
                .span = full_span,
                .lo = range_expr.binary.left,
                .hi = range_expr.binary.right,
                .inclusive = range_expr.binary.op == .range_eq,
            } });
        }

        self.reportError(.expected_type, full_span, "expected range bounds such as 'Int(0..=100)'");
        return try self.allocType(.{ .int_range = .{
            .span = full_span,
            .lo = range_expr,
            .hi = range_expr,
            .inclusive = true,
        } });
    }

    fn parseNamedType(self: *Parser) std.mem.Allocator.Error!*const ast.TypeExpr {
        const first = self.advance();
        var path: std.ArrayList(Span) = .empty;
        try path.append(self.alloc, Span.fromLoc(first.loc));
        var end_span = Span.fromLoc(first.loc);

        while (self.match(.dot) != null) {
            const seg = self.parseAnyIdentSpan("expected type path segment after '.'");
            try path.append(self.alloc, seg);
            end_span = seg;
        }

        var args: std.ArrayList(*const ast.TypeExpr) = .empty;
        if (self.match(.l_paren) != null) {
            while (!self.at(.r_paren) and !self.at(.eof)) {
                const iter_start = self.cursor;
                try args.append(self.alloc, try self.parseType());
                if (self.match(.comma) == null) break;
                if (self.cursor == iter_start) break;
            }
            const close = self.expect(.r_paren, "expected ')' after generic type arguments");
            if (close) |c| end_span = Span.fromLoc(c.loc);
        }

        return try self.allocType(.{ .named = .{
            .span = Span.merge(Span.fromLoc(first.loc), end_span),
            .path = try path.toOwnedSlice(self.alloc),
            .args = try args.toOwnedSlice(self.alloc),
        } });
    }

    fn parsePattern(self: *Parser) std.mem.Allocator.Error!*const ast.Pattern {
        return try self.parsePatternOpt(true);
    }

    fn parsePatternOpt(self: *Parser, allow_or: bool) std.mem.Allocator.Error!*const ast.Pattern {
        const first_tok = self.peek();
        if (!self.enterDepth(Span.fromLoc(first_tok.loc))) {
            return try self.allocPattern(.{ .wildcard = Span.fromLoc(first_tok.loc) });
        }
        defer self.leaveDepth();

        var pat = try self.parseAtomPattern();

        if (self.match(.kw_as) != null) {
            const alias_name = self.parseAnyIdentSpan("expected alias identifier after 'as'");
            pat = try self.allocPattern(.{ .alias = .{
                .span = Span.merge(pat.getSpan(), alias_name),
                .inner = pat,
                .name = alias_name,
            } });
        }

        if (allow_or and self.at(.bar)) {
            var alts: std.ArrayList(*const ast.Pattern) = .empty;
            try alts.append(self.alloc, pat);
            while (self.match(.bar) != null) {
                var rhs = try self.parseAtomPattern();
                if (self.match(.kw_as) != null) {
                    const alias_name = self.parseAnyIdentSpan("expected alias identifier after 'as'");
                    rhs = try self.allocPattern(.{ .alias = .{
                        .span = Span.merge(rhs.getSpan(), alias_name),
                        .inner = rhs,
                        .name = alias_name,
                    } });
                }
                try alts.append(self.alloc, rhs);
            }
            const items = try alts.toOwnedSlice(self.alloc);
            pat = try self.allocPattern(.{ .or_pat = .{
                .span = Span.merge(items[0].getSpan(), items[items.len - 1].getSpan()),
                .alternatives = items,
            } });
        }

        return pat;
    }

    fn parseAtomPattern(self: *Parser) std.mem.Allocator.Error!*const ast.Pattern {
        var pat = try self.parseSinglePattern();
        if (self.at(.dot_dot) or self.at(.dot_dot_eq)) {
            const op_tok = self.advance();
            const hi = try self.parseSinglePattern();
            pat = try self.allocPattern(.{ .range = .{
                .span = Span.merge(pat.getSpan(), hi.getSpan()),
                .lo = pat,
                .hi = hi,
                .inclusive = op_tok.tag == .dot_dot_eq,
            } });
        }
        return pat;
    }

    fn parseSinglePattern(self: *Parser) std.mem.Allocator.Error!*const ast.Pattern {
        const tok = self.peek();
        switch (tok.tag) {
            .underscore => {
                _ = self.advance();
                return try self.allocPattern(.{ .wildcard = Span.fromLoc(tok.loc) });
            },
            .kw_mut => {
                _ = self.advance();
                const name = self.parseAnyIdentSpan("expected identifier after 'mut' in pattern");
                return try self.allocPattern(.{ .ident = .{
                    .span = Span.merge(Span.fromLoc(tok.loc), name),
                    .mutable = true,
                    .name = name,
                } });
            },
            .ident => {
                if (self.peek2().tag == .dot) {
                    return try self.parseConstructorPattern();
                }
                _ = self.advance();
                return try self.allocPattern(.{ .ident = .{
                    .span = Span.fromLoc(tok.loc),
                    .mutable = false,
                    .name = Span.fromLoc(tok.loc),
                } });
            },
            .upper_ident => return try self.parseConstructorPattern(),
            .int_literal, .float_literal, .string_literal, .kw_true, .kw_false => {
                _ = self.advance();
                return try self.allocPattern(.{ .literal = .{
                    .span = Span.fromLoc(tok.loc),
                    .negative = false,
                    .tok = tok,
                } });
            },
            .minus => {
                _ = self.advance();
                const lit = self.peek();
                if (lit.tag == .int_literal or lit.tag == .float_literal) {
                    _ = self.advance();
                    return try self.allocPattern(.{ .literal = .{
                        .span = Span.merge(Span.fromLoc(tok.loc), Span.fromLoc(lit.loc)),
                        .negative = true,
                        .tok = lit,
                    } });
                }
                self.reportError(.expected_pattern, Span.fromLoc(lit.loc), "expected numeric literal after '-' in pattern");
                return try self.allocPattern(.{ .wildcard = Span.fromLoc(tok.loc) });
            },
            .l_paren => {
                _ = self.advance();
                if (self.match(.r_paren)) |close| {
                    return try self.allocPattern(.{ .tuple = .{
                        .span = Span.merge(Span.fromLoc(tok.loc), Span.fromLoc(close.loc)),
                        .elems = &.{},
                    } });
                }
                const first = try self.parsePattern();
                if (self.match(.comma) == null) {
                    _ = self.expect(.r_paren, "expected ')' closing parenthesized pattern");
                    return first;
                }
                var elems: std.ArrayList(*const ast.Pattern) = .empty;
                try elems.append(self.alloc, first);
                while (!self.at(.r_paren) and !self.at(.eof)) {
                    const iter_start = self.cursor;
                    try elems.append(self.alloc, try self.parsePattern());
                    if (self.match(.comma) == null) break;
                    if (self.cursor == iter_start) break;
                }
                const close = self.expect(.r_paren, "expected ')' closing tuple pattern");
                return try self.allocPattern(.{ .tuple = .{
                    .span = Span.merge(Span.fromLoc(tok.loc), if (close) |c| Span.fromLoc(c.loc) else elems.items[elems.items.len - 1].getSpan()),
                    .elems = try elems.toOwnedSlice(self.alloc),
                } });
            },
            .l_bracket => {
                _ = self.advance();
                var elems: std.ArrayList(*const ast.Pattern) = .empty;
                var rest: ?Span = null;
                while (!self.at(.r_bracket) and !self.at(.eof)) {
                    const iter_start = self.cursor;
                    if (self.match(.dot_dot)) |dd| {
                        rest = if (self.at(.ident) or self.at(.underscore))
                            Span.fromLoc(self.advance().loc)
                        else
                            Span.fromLoc(dd.loc);
                        _ = self.match(.comma);
                        break;
                    }
                    try elems.append(self.alloc, try self.parsePattern());
                    if (self.match(.comma) == null) break;
                    if (self.cursor == iter_start) break;
                }
                const close = self.expect(.r_bracket, "expected ']' closing list pattern");
                return try self.allocPattern(.{ .list = .{
                    .span = Span.merge(Span.fromLoc(tok.loc), if (close) |c| Span.fromLoc(c.loc) else Span.fromLoc(self.peek().loc)),
                    .elems = try elems.toOwnedSlice(self.alloc),
                    .rest = rest,
                } });
            },
            else => {
                self.reportError(.expected_pattern, Span.fromLoc(tok.loc), "expected pattern");
                if (!self.at(.eof)) _ = self.advance();
                return try self.allocPattern(.{ .wildcard = Span.fromLoc(tok.loc) });
            },
        }
    }

    fn parseConstructorPattern(self: *Parser) std.mem.Allocator.Error!*const ast.Pattern {
        const first = self.advance();
        var path: std.ArrayList(Span) = .empty;
        try path.append(self.alloc, Span.fromLoc(first.loc));
        var end_span = Span.fromLoc(first.loc);

        while (self.match(.dot) != null) {
            const seg = self.parseAnyIdentSpan("expected constructor path segment");
            try path.append(self.alloc, seg);
            end_span = seg;
        }

        var args: std.ArrayList(ast.PatternArg) = .empty;
        var has_rest = false;

        if (self.match(.l_paren) != null or (self.at(.l_brace) and self.looksLikeConstructorFieldPatternBrace())) {
            const is_brace = self.tokens[self.cursor - 1].tag == .l_brace;
            const close_tag: Token.Tag = if (is_brace) .r_brace else .r_paren;
            while (!self.at(close_tag) and !self.at(.eof)) {
                const iter_start = self.cursor;
                if (self.match(.dot_dot) != null) {
                    has_rest = true;
                    _ = self.match(.comma);
                    break;
                }
                const arg_first = self.peek();
                var label: ?Span = null;
                if (arg_first.tag == .ident and self.peek2().tag == .colon) {
                    label = Span.fromLoc(self.advance().loc);
                    _ = self.advance(); // ':'
                }
                const inner_pat = try self.parsePattern();
                try args.append(self.alloc, .{
                    .span = Span.merge(label orelse inner_pat.getSpan(), inner_pat.getSpan()),
                    .label = label,
                    .pattern = inner_pat,
                });
                if (self.match(.comma) == null) break;
                if (self.cursor == iter_start) break;
            }
            const close = self.expect(close_tag, if (is_brace) "expected '}' closing record pattern" else "expected ')' closing constructor pattern");
            if (close) |c| end_span = Span.fromLoc(c.loc);
        }

        return try self.allocPattern(.{ .constructor = .{
            .span = Span.merge(Span.fromLoc(first.loc), end_span),
            .path = try path.toOwnedSlice(self.alloc),
            .args = try args.toOwnedSlice(self.alloc),
            .has_rest = has_rest,
        } });
    }

    fn looksLikeConstructorFieldPatternBrace(self: *const Parser) bool {
        // Disambiguate `Idle { ...case body... }` vs `Entity { pos: p }`:
        // record patterns always start with `{ .. }`, `{ }`, or `{ field: ... }`.
        const next_after = self.peek2();
        if (next_after.tag == .dot_dot or next_after.tag == .r_brace) return true;
        if (next_after.tag == .ident) {
            var idx = self.cursor;
            while (idx < self.tokens.len and (self.tokens[idx].tag == .doc_comment or self.tokens[idx].tag == .module_doc_comment)) : (idx += 1) {}
            idx += 1; // skip '{'
            while (idx < self.tokens.len and (self.tokens[idx].tag == .doc_comment or self.tokens[idx].tag == .module_doc_comment)) : (idx += 1) {}
            idx += 1; // skip ident
            while (idx < self.tokens.len and (self.tokens[idx].tag == .doc_comment or self.tokens[idx].tag == .module_doc_comment)) : (idx += 1) {}
            if (idx < self.tokens.len) {
                return self.tokens[idx].tag == .colon;
            }
        }
        return false;
    }

    fn parseBlock(self: *Parser) std.mem.Allocator.Error!ast.Block {
        const open_tok = self.expect(.l_brace, "expected '{' starting block");
        const start_span = if (open_tok) |t| Span.fromLoc(t.loc) else Span.fromLoc(self.peek().loc);
        if (open_tok == null) {
            return .{
                .span = start_span,
                .attrs = &.{},
                .stmts = &.{},
                .tail = null,
            };
        }
        if (!self.enterDepth(start_span)) {
            return .{
                .span = start_span,
                .attrs = &.{},
                .stmts = &.{},
                .tail = null,
            };
        }
        defer self.leaveDepth();

        var stmts: std.ArrayList(ast.Stmt) = .empty;
        var tail: ?*const ast.Expr = null;

        while (!self.at(.r_brace) and !self.at(.eof)) {
            const iter_start = self.cursor;
            const stmt = try self.parseStmt();
            if (stmt == .expr_stmt) {
                const es = stmt.expr_stmt;
                if (!es.has_semi and es.attrs.len == 0 and self.at(.r_brace)) {
                    tail = es.expr;
                    break;
                }
            }
            try stmts.append(self.alloc, stmt);
            if (self.cursor == iter_start and !self.at(.eof)) {
                _ = self.advance();
            }
        }

        const close = self.expect(.r_brace, "expected '}' closing block");
        const end_span = if (close) |c| Span.fromLoc(c.loc) else self.lastConsumedSpan(self.peek());
        return .{
            .span = Span.merge(start_span, end_span),
            .attrs = &.{},
            .stmts = try stmts.toOwnedSlice(self.alloc),
            .tail = tail,
        };
    }

    fn parseStmt(self: *Parser) std.mem.Allocator.Error!ast.Stmt {
        const attrs = try self.parseAttributes();
        const head = self.peek();
        const attr_start = if (attrs.len > 0) attrs[0].span else Span.fromLoc(head.loc);

        switch (head.tag) {
            .kw_let => {
                _ = self.advance();
                const is_mut = self.match(.kw_mut) != null;
                const pat = try self.parsePattern();
                var ty: ?*const ast.TypeExpr = null;
                if (self.match(.colon) != null) {
                    ty = try self.parseType();
                }
                _ = self.expect(.eq, "expected '=' in let binding");
                const val = try self.parseExprPrec(1, true);
                const semi = self.match(.semicolon);
                return .{ .let_stmt = .{
                    .span = Span.merge(attr_start, if (semi) |s| Span.fromLoc(s.loc) else val.getSpan()),
                    .attrs = attrs,
                    .mutable = is_mut,
                    .pattern = pat,
                    .ty = ty,
                    .value = val,
                } };
            },
            .kw_use => {
                _ = self.advance();
                var pats: std.ArrayList(*const ast.Pattern) = .empty;
                if (!self.at(.left_arrow)) {
                    while (!self.at(.left_arrow) and !self.at(.eof)) {
                        const iter_start = self.cursor;
                        try pats.append(self.alloc, try self.parsePattern());
                        if (self.match(.comma) == null) break;
                        if (self.cursor == iter_start) break;
                    }
                }
                _ = self.expect(.left_arrow, "expected '<-' in use statement");
                const expr = try self.parseExprPrec(1, true);
                const semi = self.match(.semicolon);
                return .{ .use_stmt = .{
                    .span = Span.merge(attr_start, if (semi) |s| Span.fromLoc(s.loc) else expr.getSpan()),
                    .patterns = try pats.toOwnedSlice(self.alloc),
                    .expr = expr,
                } };
            },
            .kw_return => {
                _ = self.advance();
                var val: ?*const ast.Expr = null;
                if (!self.at(.semicolon) and !self.at(.r_brace) and !self.at(.eof)) {
                    val = try self.parseExprPrec(1, true);
                }
                const semi = self.match(.semicolon);
                const end_span = if (semi) |s|
                    Span.fromLoc(s.loc)
                else if (val) |v|
                    v.getSpan()
                else
                    Span.fromLoc(head.loc);
                return .{ .return_stmt = .{
                    .span = Span.merge(attr_start, end_span),
                    .value = val,
                } };
            },
            .kw_while => {
                _ = self.advance();
                const cond = try self.parseExprPrec(1, false);
                var decreases: ?*const ast.Expr = null;
                if (self.atContextual(.decreases)) {
                    _ = self.advance();
                    decreases = try self.parseExprPrec(1, false);
                }
                const body = try self.parseBlock();
                _ = self.match(.semicolon);
                return .{ .while_stmt = .{
                    .span = Span.merge(attr_start, body.span),
                    .cond = cond,
                    .decreases = decreases,
                    .body = body,
                } };
            },
            .kw_for => {
                _ = self.advance();
                const pat = try self.parsePattern();
                _ = self.expect(.kw_in, "expected 'in' in for loop");
                const iter = try self.parseExprPrec(1, false);
                var decreases: ?*const ast.Expr = null;
                if (self.atContextual(.decreases)) {
                    _ = self.advance();
                    decreases = try self.parseExprPrec(1, false);
                }
                const body = try self.parseBlock();
                _ = self.match(.semicolon);
                return .{ .for_stmt = .{
                    .span = Span.merge(attr_start, body.span),
                    .pattern = pat,
                    .iter = iter,
                    .decreases = decreases,
                    .body = body,
                } };
            },
            else => {
                const expr = try self.parseExprPrec(1, true);
                if (assignOpOf(self.peek().tag)) |aop| {
                    _ = self.advance();
                    const rhs = try self.parseExprPrec(1, true);
                    const semi = self.match(.semicolon);
                    return .{ .assign_stmt = .{
                        .span = Span.merge(attr_start, if (semi) |s| Span.fromLoc(s.loc) else rhs.getSpan()),
                        .target = expr,
                        .op = aop,
                        .value = rhs,
                    } };
                }
                const semi = self.match(.semicolon);
                return .{ .expr_stmt = .{
                    .span = Span.merge(attr_start, if (semi) |s| Span.fromLoc(s.loc) else expr.getSpan()),
                    .attrs = attrs,
                    .expr = expr,
                    .has_semi = semi != null,
                } };
            },
        }
    }

    fn assignOpOf(tag: Token.Tag) ?ast.AssignOp {
        return switch (tag) {
            .eq => .assign,
            .plus_eq => .add_assign,
            .minus_eq => .sub_assign,
            .star_eq => .mul_assign,
            .slash_eq => .div_assign,
            .percent_eq => .rem_assign,
            else => null,
        };
    }

    fn binaryOpInfo(tag: Token.Tag) ?struct { op: ast.BinaryOp, prec: u8, right_assoc: bool } {
        return switch (tag) {
            .pipe => .{ .op = .pipe, .prec = 1, .right_assoc = false },
            .dot_dot => .{ .op = .range, .prec = 2, .right_assoc = false },
            .dot_dot_eq => .{ .op = .range_eq, .prec = 2, .right_assoc = false },
            .pipe_pipe => .{ .op = .or_op, .prec = 3, .right_assoc = false },
            .amp_amp => .{ .op = .and_op, .prec = 4, .right_assoc = false },
            .eq_eq => .{ .op = .eq, .prec = 5, .right_assoc = false },
            .bang_eq => .{ .op = .ne, .prec = 5, .right_assoc = false },
            .lt => .{ .op = .lt, .prec = 5, .right_assoc = false },
            .lt_eq => .{ .op = .le, .prec = 5, .right_assoc = false },
            .gt => .{ .op = .gt, .prec = 5, .right_assoc = false },
            .gt_eq => .{ .op = .ge, .prec = 5, .right_assoc = false },
            .bar => .{ .op = .bit_or, .prec = 6, .right_assoc = false },
            .caret => .{ .op = .bit_xor, .prec = 7, .right_assoc = false },
            .amp => .{ .op = .bit_and, .prec = 8, .right_assoc = false },
            .lt_lt => .{ .op = .shl, .prec = 9, .right_assoc = false },
            .gt_gt => .{ .op = .shr, .prec = 9, .right_assoc = false },
            .plus => .{ .op = .add, .prec = 10, .right_assoc = false },
            .minus => .{ .op = .sub, .prec = 10, .right_assoc = false },
            .plus_percent => .{ .op = .add_wrap, .prec = 10, .right_assoc = false },
            .minus_percent => .{ .op = .sub_wrap, .prec = 10, .right_assoc = false },
            .plus_pipe => .{ .op = .add_sat, .prec = 10, .right_assoc = false },
            .minus_pipe => .{ .op = .sub_sat, .prec = 10, .right_assoc = false },
            .lt_gt => .{ .op = .concat, .prec = 10, .right_assoc = false },
            .star => .{ .op = .mul, .prec = 11, .right_assoc = false },
            .slash => .{ .op = .div, .prec = 11, .right_assoc = false },
            .percent => .{ .op = .rem, .prec = 11, .right_assoc = false },
            .star_percent => .{ .op = .mul_wrap, .prec = 11, .right_assoc = false },
            .star_pipe => .{ .op = .mul_sat, .prec = 11, .right_assoc = false },
            else => null,
        };
    }

    fn parseExprPrec(self: *Parser, min_prec: u8, allow_struct_lit: bool) std.mem.Allocator.Error!*const ast.Expr {
        const start_tok = self.peek();
        if (!self.enterDepth(Span.fromLoc(start_tok.loc))) {
            return try self.makeErrExpr(Span.fromLoc(start_tok.loc));
        }
        defer self.leaveDepth();

        var lhs = try self.parsePrefixExpr(allow_struct_lit);

        while (true) {
            const cur = self.peek();
            // Cast operator (`expr as Type`) sits at precedence 12 (tighter than `*`, looser than unary `-`).
            if (cur.tag == .kw_as and 12 >= min_prec) {
                _ = self.advance();
                const ty = try self.parseType();
                lhs = try self.allocExpr(.{ .cast = .{
                    .span = Span.merge(lhs.getSpan(), ty.getSpan()),
                    .expr = lhs,
                    .ty = ty,
                } });
                continue;
            }

            if (binaryOpInfo(cur.tag)) |info| {
                if (info.prec < min_prec) break;
                _ = self.advance();
                const next_min = if (info.right_assoc) info.prec else info.prec + 1;
                const rhs = try self.parseExprPrec(next_min, allow_struct_lit);
                lhs = try self.allocExpr(.{ .binary = .{
                    .span = Span.merge(lhs.getSpan(), rhs.getSpan()),
                    .op = info.op,
                    .left = lhs,
                    .right = rhs,
                } });
                continue;
            }
            break;
        }

        return lhs;
    }

    fn parsePrefixExpr(self: *Parser, allow_struct_lit: bool) std.mem.Allocator.Error!*const ast.Expr {
        const tok = self.peek();
        const uop: ?ast.UnaryOp = switch (tok.tag) {
            .minus => .neg,
            .bang => .not,
            .tilde => .bit_not,
            .kw_move => .move_op,
            .amp => .addr_of,
            else => null,
        };
        if (uop) |op| {
            _ = self.advance();
            const operand = try self.parsePrefixExpr(allow_struct_lit);
            return try self.allocExpr(.{ .unary = .{
                .span = Span.merge(Span.fromLoc(tok.loc), operand.getSpan()),
                .op = op,
                .operand = operand,
            } });
        }
        return try self.parsePostfixExpr(allow_struct_lit);
    }

    fn hasNewlineBetween(self: *const Parser, from: usize, to: usize) bool {
        if (from >= to or to > self.source.len) return false;
        return std.mem.indexOfScalar(u8, self.source[from..to], '\n') != null;
    }

    fn parsePostfixExpr(self: *Parser, allow_struct_lit: bool) std.mem.Allocator.Error!*const ast.Expr {
        var expr = try self.parsePrimaryExpr(allow_struct_lit);

        while (true) {
            const cur = self.peek();
            switch (cur.tag) {
                .l_paren => {
                    if (self.hasNewlineBetween(expr.getSpan().end, cur.loc.start)) break;
                    _ = self.advance();
                    var args: std.ArrayList(ast.CallArg) = .empty;
                    while (!self.at(.r_paren) and !self.at(.eof)) {
                        const iter_start = self.cursor;
                        const first = self.peek();
                        var label: ?Span = null;
                        if (first.tag == .ident and self.peek2().tag == .colon) {
                            label = Span.fromLoc(self.advance().loc);
                            _ = self.advance(); // ':'
                        }
                        const val = try self.parseExprPrec(1, true);
                        try args.append(self.alloc, .{
                            .span = Span.merge(label orelse val.getSpan(), val.getSpan()),
                            .label = label,
                            .value = val,
                        });
                        if (self.match(.comma) == null) break;
                        if (self.cursor == iter_start) break;
                    }
                    const close = self.expect(.r_paren, "expected ')' after function call arguments");
                    const end_span = if (close) |c| Span.fromLoc(c.loc) else self.lastConsumedSpan(cur);
                    expr = try self.allocExpr(.{ .call = .{
                        .span = Span.merge(expr.getSpan(), end_span),
                        .callee = expr,
                        .args = try args.toOwnedSlice(self.alloc),
                    } });
                },
                .dot => {
                    _ = self.advance();
                    const mem = self.peek();
                    if (mem.tag == .ident or mem.tag == .upper_ident or mem.tag == .int_literal) {
                        _ = self.advance();
                        expr = try self.allocExpr(.{ .field = .{
                            .span = Span.merge(expr.getSpan(), Span.fromLoc(mem.loc)),
                            .target = expr,
                            .name = Span.fromLoc(mem.loc),
                        } });
                    } else {
                        self.reportError(.expected_token, Span.fromLoc(mem.loc), "expected field name or tuple index after '.'");
                    }
                },
                .l_bracket => {
                    if (self.hasNewlineBetween(expr.getSpan().end, cur.loc.start)) break;
                    _ = self.advance();
                    const idx = try self.parseExprPrec(1, true);
                    const close = self.expect(.r_bracket, "expected ']' closing index expression");
                    const end_span = if (close) |c| Span.fromLoc(c.loc) else idx.getSpan();
                    expr = try self.allocExpr(.{ .index = .{
                        .span = Span.merge(expr.getSpan(), end_span),
                        .target = expr,
                        .idx = idx,
                    } });
                },
                .question => {
                    const q = self.advance();
                    expr = try self.allocExpr(.{ .try_op = .{
                        .span = Span.merge(expr.getSpan(), Span.fromLoc(q.loc)),
                        .operand = expr,
                    } });
                },
                .l_brace => {
                    if (allow_struct_lit) {
                        if (try self.tryExtractUpperPath(expr)) |path| {
                            expr = try self.parseRecordLitBody(expr.getSpan(), path);
                            continue;
                        }
                    }
                    break;
                },
                else => break,
            }
        }
        return expr;
    }

    fn tryExtractUpperPath(self: *Parser, expr: *const ast.Expr) std.mem.Allocator.Error!?[]const Span {
        // Record literals apply strictly to capitalized type names or module-qualified type names
        // (e.g., `Entity { ... }` or `geom.Vec2 { ... }`).
        var rev: std.ArrayList(Span) = .empty;
        var cur = expr;
        var ends_upper = false;
        while (true) {
            switch (cur.*) {
                .upper_ident => |s| {
                    if (rev.items.len == 0) ends_upper = true;
                    try rev.append(self.alloc, s);
                    break;
                },
                .ident => |s| {
                    if (rev.items.len == 0) return null;
                    try rev.append(self.alloc, s);
                    break;
                },
                .field => |f| {
                    if (rev.items.len == 0) {
                        const tail_slice = f.name.slice(self.source);
                        if (tail_slice.len == 0 or tail_slice[0] < 'A' or tail_slice[0] > 'Z') {
                            return null;
                        }
                        ends_upper = true;
                    }
                    try rev.append(self.alloc, f.name);
                    cur = f.target;
                },
                else => return null,
            }
        }
        if (!ends_upper or rev.items.len == 0) return null;
        std.mem.reverse(Span, rev.items);
        return try rev.toOwnedSlice(self.alloc);
    }

    fn parseRecordLitBody(self: *Parser, path_span: Span, path: []const Span) std.mem.Allocator.Error!*const ast.Expr {
        const open = self.advance(); // '{'
        var fields: std.ArrayList(ast.RecordFieldInit) = .empty;
        while (!self.at(.r_brace) and !self.at(.eof)) {
            const iter_start = self.cursor;
            const fname = self.parseAnyIdentSpan("expected field name in record literal");
            var val: ?*const ast.Expr = null;
            var end_span = fname;
            if (self.match(.colon) != null) {
                const v = try self.parseExprPrec(1, true);
                val = v;
                end_span = v.getSpan();
            }
            try fields.append(self.alloc, .{
                .span = Span.merge(fname, end_span),
                .name = fname,
                .value = val,
            });
            if (self.match(.comma) == null) break;
            if (self.cursor == iter_start) break;
        }
        const close = self.expect(.r_brace, "expected '}' closing record literal");
        const close_span = if (close) |c| Span.fromLoc(c.loc) else Span.fromLoc(open.loc);
        return try self.allocExpr(.{ .record_lit = .{
            .span = Span.merge(path_span, close_span),
            .path = path,
            .fields = try fields.toOwnedSlice(self.alloc),
        } });
    }

    fn parsePrimaryExpr(self: *Parser, allow_struct_lit: bool) std.mem.Allocator.Error!*const ast.Expr {
        _ = allow_struct_lit;
        const tok = self.peek();
        switch (tok.tag) {
            .int_literal => {
                _ = self.advance();
                return try self.allocExpr(.{ .int_lit = Span.fromLoc(tok.loc) });
            },
            .float_literal => {
                _ = self.advance();
                return try self.allocExpr(.{ .float_lit = Span.fromLoc(tok.loc) });
            },
            .string_literal => {
                _ = self.advance();
                return try self.allocExpr(.{ .string_lit = Span.fromLoc(tok.loc) });
            },
            .kw_true => {
                _ = self.advance();
                return try self.allocExpr(.{ .bool_lit = .{ .span = Span.fromLoc(tok.loc), .value = true } });
            },
            .kw_false => {
                _ = self.advance();
                return try self.allocExpr(.{ .bool_lit = .{ .span = Span.fromLoc(tok.loc), .value = false } });
            },
            .underscore => {
                _ = self.advance();
                return try self.allocExpr(.{ .placeholder = Span.fromLoc(tok.loc) });
            },
            .upper_ident => {
                _ = self.advance();
                return try self.allocExpr(.{ .upper_ident = Span.fromLoc(tok.loc) });
            },
            .ident => {
                if (self.atContextual(.fork) and self.peek2().tag == .l_brace) {
                    return try self.parseForkExpr();
                }
                _ = self.advance();
                return try self.allocExpr(.{ .ident = Span.fromLoc(tok.loc) });
            },
            .l_paren => {
                _ = self.advance();
                if (self.match(.r_paren)) |close| {
                    return try self.allocExpr(.{ .tuple = .{
                        .span = Span.merge(Span.fromLoc(tok.loc), Span.fromLoc(close.loc)),
                        .elems = &.{},
                    } });
                }
                const first = try self.parseExprPrec(1, true);
                if (self.match(.comma) == null) {
                    _ = self.expect(.r_paren, "expected ')' closing parenthesized expression");
                    return first;
                }
                var elems: std.ArrayList(*const ast.Expr) = .empty;
                try elems.append(self.alloc, first);
                while (!self.at(.r_paren) and !self.at(.eof)) {
                    const iter_start = self.cursor;
                    try elems.append(self.alloc, try self.parseExprPrec(1, true));
                    if (self.match(.comma) == null) break;
                    if (self.cursor == iter_start) break;
                }
                const close = self.expect(.r_paren, "expected ')' closing tuple expression");
                return try self.allocExpr(.{ .tuple = .{
                    .span = Span.merge(Span.fromLoc(tok.loc), if (close) |c| Span.fromLoc(c.loc) else elems.items[elems.items.len - 1].getSpan()),
                    .elems = try elems.toOwnedSlice(self.alloc),
                } });
            },
            .l_bracket => {
                _ = self.advance();
                var elems: std.ArrayList(*const ast.Expr) = .empty;
                while (!self.at(.r_bracket) and !self.at(.eof)) {
                    const iter_start = self.cursor;
                    try elems.append(self.alloc, try self.parseExprPrec(1, true));
                    if (self.match(.comma) == null) break;
                    if (self.cursor == iter_start) break;
                }
                const close = self.expect(.r_bracket, "expected ']' closing list literal");
                return try self.allocExpr(.{ .list = .{
                    .span = Span.merge(Span.fromLoc(tok.loc), if (close) |c| Span.fromLoc(c.loc) else Span.fromLoc(self.peek().loc)),
                    .elems = try elems.toOwnedSlice(self.alloc),
                } });
            },
            .l_brace => {
                const blk = try self.parseBlock();
                return try self.allocExpr(.{ .block = blk });
            },
            .kw_if => return try self.parseIfExpr(),
            .kw_case => return try self.parseCaseExpr(),
            .kw_fn => return try self.parseLambdaExpr(),
            .kw_view => return try self.parseViewExpr(),
            .kw_todo, .kw_panic => {
                _ = self.advance();
                var msg: ?*const ast.Expr = null;
                var end_span = Span.fromLoc(tok.loc);
                if (self.match(.kw_as) != null) {
                    const m = try self.parseExprPrec(1, true);
                    msg = m;
                    end_span = m.getSpan();
                } else if (self.match(.l_paren) != null) {
                    if (!self.at(.r_paren)) {
                        msg = try self.parseExprPrec(1, true);
                    }
                    const close = self.expect(.r_paren, "expected ')'");
                    if (close) |c| end_span = Span.fromLoc(c.loc);
                }
                if (tok.tag == .kw_todo) {
                    return try self.allocExpr(.{ .todo_expr = .{
                        .span = Span.merge(Span.fromLoc(tok.loc), end_span),
                        .message = msg,
                    } });
                } else {
                    return try self.allocExpr(.{ .panic_expr = .{
                        .span = Span.merge(Span.fromLoc(tok.loc), end_span),
                        .message = msg,
                    } });
                }
            },
            else => {
                self.reportError(.expected_expr, Span.fromLoc(tok.loc), "expected expression");
                if (!self.at(.eof)) _ = self.advance();
                return try self.makeErrExpr(Span.fromLoc(tok.loc));
            },
        }
    }

    fn parseIfExpr(self: *Parser) std.mem.Allocator.Error!*const ast.Expr {
        const if_tok = self.advance(); // 'if'
        const cond = try self.parseExprPrec(1, false);
        const then_blk = try self.parseBlock();
        var end_span = then_blk.span;
        var else_branch: ?*const ast.Expr = null;

        if (self.match(.kw_else) != null) {
            if (self.at(.kw_if)) {
                const nested_if = try self.parseIfExpr();
                else_branch = nested_if;
                end_span = nested_if.getSpan();
            } else {
                const else_blk = try self.parseBlock();
                end_span = else_blk.span;
                else_branch = try self.allocExpr(.{ .block = else_blk });
            }
        }

        return try self.allocExpr(.{ .if_expr = .{
            .span = Span.merge(Span.fromLoc(if_tok.loc), end_span),
            .cond = cond,
            .then_block = then_blk,
            .else_branch = else_branch,
        } });
    }

    fn parseCaseExpr(self: *Parser) std.mem.Allocator.Error!*const ast.Expr {
        const case_tok = self.advance(); // 'case'
        var subjects: std.ArrayList(*const ast.Expr) = .empty;
        while (!self.at(.l_brace) and !self.at(.eof)) {
            const iter_start = self.cursor;
            try subjects.append(self.alloc, try self.parseExprPrec(1, false));
            if (self.match(.comma) == null) break;
            if (self.cursor == iter_start) break;
        }
        _ = self.expect(.l_brace, "expected '{' after case subjects");

        var arms: std.ArrayList(ast.CaseArm) = .empty;
        while (!self.at(.r_brace) and !self.at(.eof)) {
            const iter_start = self.cursor;
            var alts: std.ArrayList([]const *const ast.Pattern) = .empty;
            while (!self.at(.kw_if) and !self.at(.arrow) and !self.at(.fat_arrow) and !self.at(.r_brace) and !self.at(.eof)) {
                const alt_start = self.cursor;
                var row: std.ArrayList(*const ast.Pattern) = .empty;
                while (!self.at(.bar) and !self.at(.kw_if) and !self.at(.arrow) and !self.at(.fat_arrow) and !self.at(.r_brace) and !self.at(.eof)) {
                    const pat_start = self.cursor;
                    try row.append(self.alloc, try self.parsePatternOpt(false));
                    if (self.match(.comma) == null) break;
                    if (self.cursor == pat_start) break;
                }
                try alts.append(self.alloc, try row.toOwnedSlice(self.alloc));
                if (self.match(.bar) == null) break;
                if (self.cursor == alt_start) break;
            }
            var guard: ?*const ast.Expr = null;
            if (self.match(.kw_if) != null) {
                guard = try self.parseExprPrec(1, false);
            }
            if (self.match(.arrow) == null and self.match(.fat_arrow) == null) {
                self.reportError(.expected_token, Span.fromLoc(self.peek().loc), "expected '->' or '=>' in case arm");
            }
            const body = try self.parseExprPrec(1, true);
            const arm_start = if (alts.items.len > 0 and alts.items[0].len > 0) alts.items[0][0].getSpan() else body.getSpan();
            try arms.append(self.alloc, .{
                .span = Span.merge(arm_start, body.getSpan()),
                .alternatives = try alts.toOwnedSlice(self.alloc),
                .guard = guard,
                .body = body,
            });
            _ = self.match(.comma);
            _ = self.match(.semicolon);
            if (self.cursor == iter_start and !self.at(.eof)) _ = self.advance();
        }
        const close = self.expect(.r_brace, "expected '}' closing case expression");
        return try self.allocExpr(.{ .case_expr = .{
            .span = Span.merge(Span.fromLoc(case_tok.loc), if (close) |c| Span.fromLoc(c.loc) else self.lastConsumedSpan(case_tok)),
            .subjects = try subjects.toOwnedSlice(self.alloc),
            .arms = try arms.toOwnedSlice(self.alloc),
        } });
    }

    fn parseLambdaExpr(self: *Parser) std.mem.Allocator.Error!*const ast.Expr {
        const fn_tok = self.advance(); // 'fn'
        const params = try self.parseParamList(false);
        var ret: ?*const ast.TypeExpr = null;
        if (self.match(.arrow) != null) {
            ret = try self.parseType();
        }
        const body = try self.parseBlock();
        return try self.allocExpr(.{ .lambda = .{
            .span = Span.merge(Span.fromLoc(fn_tok.loc), body.span),
            .params = params,
            .ret = ret,
            .body = body,
        } });
    }

    fn parseViewExpr(self: *Parser) std.mem.Allocator.Error!*const ast.Expr {
        const view_tok = self.advance(); // 'view'
        var mode: ?ast.BorrowMode = null;
        if (self.atContextual(.shared)) {
            _ = self.advance();
            mode = .shared;
        } else if (self.atContextual(.exclusive)) {
            _ = self.advance();
            mode = .exclusive;
        } else if (self.match(.kw_mut) != null) {
            mode = .exclusive;
        }

        var binding: ?Span = null;
        if (self.at(.ident) and self.peek2().tag == .eq) {
            binding = Span.fromLoc(self.advance().loc);
            _ = self.advance(); // '='
        }

        const target = try self.parseExprPrec(1, false);
        const body = try self.parseBlock();
        return try self.allocExpr(.{ .view_expr = .{
            .span = Span.merge(Span.fromLoc(view_tok.loc), body.span),
            .mode = mode,
            .binding = binding,
            .target = target,
            .body = body,
        } });
    }

    fn parseForkExpr(self: *Parser) std.mem.Allocator.Error!*const ast.Expr {
        const fork_tok = self.advance(); // 'fork'
        var branches: std.ArrayList(ast.Block) = .empty;
        var end_span = Span.fromLoc(fork_tok.loc);

        if (self.match(.l_brace) != null) {
            if (self.at(.l_brace)) {
                while (self.at(.l_brace) and !self.at(.eof)) {
                    const iter_start = self.cursor;
                    try branches.append(self.alloc, try self.parseBlock());
                    _ = self.match(.comma);
                    if (self.cursor == iter_start) break;
                }
                const close = self.expect(.r_brace, "expected '}' closing fork branches");
                if (close) |c| end_span = Span.fromLoc(c.loc);
            } else {
                // Rewind cursor one step so `parseBlock` owns the opening brace of a single block.
                // Actually parse statements directly inside this fork block for zero backtracking!
                var stmts: std.ArrayList(ast.Stmt) = .empty;
                var tail: ?*const ast.Expr = null;
                while (!self.at(.r_brace) and !self.at(.eof)) {
                    const iter_start = self.cursor;
                    const stmt = try self.parseStmt();
                    if (stmt == .expr_stmt) {
                        const es = stmt.expr_stmt;
                        if (!es.has_semi and es.attrs.len == 0 and self.at(.r_brace)) {
                            tail = es.expr;
                            break;
                        }
                    }
                    try stmts.append(self.alloc, stmt);
                    if (self.cursor == iter_start and !self.at(.eof)) _ = self.advance();
                }
                const close = self.expect(.r_brace, "expected '}' closing fork block");
                end_span = if (close) |c| Span.fromLoc(c.loc) else self.lastConsumedSpan(fork_tok);
                try branches.append(self.alloc, .{
                    .span = Span.merge(Span.fromLoc(fork_tok.loc), end_span),
                    .attrs = &.{},
                    .stmts = try stmts.toOwnedSlice(self.alloc),
                    .tail = tail,
                });
            }
        } else {
            self.reportError(.expected_token, Span.fromLoc(self.peek().loc), "expected '{' after 'fork'");
        }

        var explicit_join = false;
        if (self.atContextual(.join)) {
            const jtok = self.advance();
            explicit_join = true;
            end_span = Span.fromLoc(jtok.loc);
        }

        return try self.allocExpr(.{ .fork_expr = .{
            .span = Span.merge(Span.fromLoc(fork_tok.loc), end_span),
            .branches = try branches.toOwnedSlice(self.alloc),
            .explicit_join = explicit_join,
        } });
    }
};
