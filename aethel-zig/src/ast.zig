const std = @import("std");
const Io = std.Io;
const lexer = @import("lexer.zig");

/// Byte offset range `[start..end)` within `Ast.source`.
pub const Span = struct {
    start: usize,
    end: usize,

    pub fn fromLoc(loc: lexer.Loc) Span {
        return .{ .start = loc.start, .end = loc.end };
    }

    pub fn merge(a: Span, b: Span) Span {
        return .{
            .start = @min(a.start, b.start),
            .end = @max(a.end, b.end),
        };
    }

    pub fn slice(self: Span, source: []const u8) []const u8 {
        if (self.start > self.end or self.end > source.len) return "";
        return source[self.start..self.end];
    }
};

pub const Diagnostic = struct {
    span: Span,
    kind: Kind,
    message: []const u8,

    pub const Kind = enum {
        lexer_error,
        unexpected_token,
        expected_token,
        expected_expr,
        expected_type,
        expected_pattern,
        expected_decl,
        invalid_attribute,
        invalid_law_clause,
        invalid_extern_abi,
        nesting_depth_exceeded,
    };
};

pub const FieldPath = []const Span;

pub const BorrowMode = enum {
    shared,
    exclusive,
};

pub const PathBorrow = struct {
    span: Span,
    mode: ?BorrowMode,
    paths: []const FieldPath,
};

pub const LayoutSpec = union(enum) {
    aos,
    soa,
    aosoa: ?*const Expr,
    auto,
    @"packed",
    flat,
};

pub const TraitParam = struct {
    span: Span,
    name: Span,
    arity: u8,
};

pub const TraitConstraint = struct {
    span: Span,
    path: []const Span,
    args: []const *const TypeExpr,
};

pub const TraitMethodSig = struct {
    span: Span,
    doc_comments: []const Span,
    name: Span,
    params: []const Param,
    ret: ?*const TypeExpr,
};

pub const TraitLaw = struct {
    span: Span,
    name: Span,
    params: []const Param,
    clauses: []const LawClause,
};

pub const InstanceMethod = struct {
    span: Span,
    name: Span,
    params: []const Param,
    ret: ?*const TypeExpr,
    body: Block,
};

pub const Attribute = struct {
    span: Span,
    name: Span,
    payload: Payload,

    pub const Payload = union(enum) {
        none,
        layout: LayoutSpec,
        args: []const *const Expr,
    };
};

pub const TypeExpr = union(enum) {
    primitive: struct {
        span: Span,
        prim: lexer.PrimitiveType,
    },
    int_range: struct {
        span: Span,
        lo: *const Expr,
        hi: *const Expr,
        inclusive: bool,
    },
    named: struct {
        span: Span,
        path: []const Span,
        args: []const *const TypeExpr,
    },
    type_var: struct {
        span: Span,
        name: Span,
    },
    path_borrow: struct {
        span: Span,
        base: *const TypeExpr,
        borrow: PathBorrow,
    },
    fn_type: struct {
        span: Span,
        params: []const *const TypeExpr,
        ret: *const TypeExpr,
        is_once: bool = false,
    },
    tuple: struct {
        span: Span,
        elems: []const *const TypeExpr,
    },
    slice: struct {
        span: Span,
        mutable: bool,
        elem: *const TypeExpr,
    },
    inferred: Span,

    pub fn getSpan(self: TypeExpr) Span {
        return switch (self) {
            .primitive => |v| v.span,
            .int_range => |v| v.span,
            .named => |v| v.span,
            .type_var => |v| v.span,
            .path_borrow => |v| v.span,
            .fn_type => |v| v.span,
            .tuple => |v| v.span,
            .slice => |v| v.span,
            .inferred => |s| s,
        };
    }
};

pub const PatternArg = struct {
    span: Span,
    label: ?Span,
    pattern: *const Pattern,
};

pub const Pattern = union(enum) {
    wildcard: Span,
    ident: struct {
        span: Span,
        mutable: bool,
        name: Span,
    },
    literal: struct {
        span: Span,
        negative: bool,
        tok: lexer.Token,
    },
    range: struct {
        span: Span,
        lo: *const Pattern,
        hi: *const Pattern,
        inclusive: bool,
    },
    tuple: struct {
        span: Span,
        elems: []const *const Pattern,
    },
    list: struct {
        span: Span,
        elems: []const *const Pattern,
        rest: ?Span,
    },
    constructor: struct {
        span: Span,
        path: []const Span,
        args: []const PatternArg,
        has_rest: bool,
    },
    alias: struct {
        span: Span,
        inner: *const Pattern,
        name: Span,
    },
    or_pat: struct {
        span: Span,
        alternatives: []const *const Pattern,
    },

    pub fn getSpan(self: Pattern) Span {
        return switch (self) {
            .wildcard => |s| s,
            .ident => |v| v.span,
            .literal => |v| v.span,
            .range => |v| v.span,
            .tuple => |v| v.span,
            .list => |v| v.span,
            .constructor => |v| v.span,
            .alias => |v| v.span,
            .or_pat => |v| v.span,
        };
    }
};

pub const BinaryOp = enum {
    pipe,
    range,
    range_eq,
    or_op,
    and_op,
    eq,
    ne,
    lt,
    le,
    gt,
    ge,
    bit_or,
    bit_xor,
    bit_and,
    shl,
    shr,
    add,
    sub,
    add_wrap,
    sub_wrap,
    add_sat,
    sub_sat,
    concat,
    mul,
    div,
    rem,
    mul_wrap,
    mul_sat,

    pub fn symbol(self: BinaryOp) []const u8 {
        return switch (self) {
            .pipe => "|>",
            .range => "..",
            .range_eq => "..=",
            .or_op => "||",
            .and_op => "&&",
            .eq => "==",
            .ne => "!=",
            .lt => "<",
            .le => "<=",
            .gt => ">",
            .ge => ">=",
            .bit_or => "|",
            .bit_xor => "^",
            .bit_and => "&",
            .shl => "<<",
            .shr => ">>",
            .add => "+",
            .sub => "-",
            .add_wrap => "+%",
            .sub_wrap => "-%",
            .add_sat => "+|",
            .sub_sat => "-|",
            .concat => "<>",
            .mul => "*",
            .div => "/",
            .rem => "%",
            .mul_wrap => "*%",
            .mul_sat => "*|",
        };
    }
};

pub const UnaryOp = enum {
    neg,
    not,
    bit_not,
    move_op,
    addr_of,

    pub fn symbol(self: UnaryOp) []const u8 {
        return switch (self) {
            .neg => "-",
            .not => "!",
            .bit_not => "~",
            .move_op => "move",
            .addr_of => "&",
        };
    }
};

pub const AssignOp = enum {
    assign,
    add_assign,
    sub_assign,
    mul_assign,
    div_assign,
    rem_assign,

    pub fn symbol(self: AssignOp) []const u8 {
        return switch (self) {
            .assign => "=",
            .add_assign => "+=",
            .sub_assign => "-=",
            .mul_assign => "*=",
            .div_assign => "/=",
            .rem_assign => "%=",
        };
    }
};

pub const CallArg = struct {
    span: Span,
    label: ?Span,
    value: *const Expr,
};

pub const RecordFieldInit = struct {
    span: Span,
    name: Span,
    value: ?*const Expr,
};

pub const Param = struct {
    span: Span,
    label: ?Span,
    mutable: bool,
    name: Span,
    ty: ?*const TypeExpr,
};

pub const Block = struct {
    span: Span,
    attrs: []const Attribute,
    stmts: []const Stmt,
    tail: ?*const Expr,
};

pub const CaseArm = struct {
    span: Span,
    alternatives: []const []const *const Pattern,
    guard: ?*const Expr,
    body: *const Expr,
};

pub const Expr = union(enum) {
    int_lit: Span,
    float_lit: Span,
    string_lit: Span,
    bool_lit: struct {
        span: Span,
        value: bool,
    },
    ident: Span,
    upper_ident: Span,
    placeholder: Span,
    unary: struct {
        span: Span,
        op: UnaryOp,
        operand: *const Expr,
    },
    binary: struct {
        span: Span,
        op: BinaryOp,
        left: *const Expr,
        right: *const Expr,
    },
    cast: struct {
        span: Span,
        expr: *const Expr,
        ty: *const TypeExpr,
    },
    call: struct {
        span: Span,
        callee: *const Expr,
        args: []const CallArg,
    },
    field: struct {
        span: Span,
        target: *const Expr,
        name: Span,
    },
    index: struct {
        span: Span,
        target: *const Expr,
        idx: *const Expr,
    },
    try_op: struct {
        span: Span,
        operand: *const Expr,
    },
    record_lit: struct {
        span: Span,
        path: []const Span,
        fields: []const RecordFieldInit,
    },
    tuple: struct {
        span: Span,
        elems: []const *const Expr,
    },
    list: struct {
        span: Span,
        elems: []const *const Expr,
    },
    block: Block,
    if_expr: struct {
        span: Span,
        cond: *const Expr,
        then_block: Block,
        else_branch: ?*const Expr,
    },
    case_expr: struct {
        span: Span,
        subjects: []const *const Expr,
        arms: []const CaseArm,
    },
    lambda: struct {
        span: Span,
        params: []const Param,
        ret: ?*const TypeExpr,
        body: Block,
        is_once: bool = false,
    },
    view_expr: struct {
        span: Span,
        mode: ?BorrowMode,
        binding: ?Span,
        target: *const Expr,
        body: Block,
    },
    fork_expr: struct {
        span: Span,
        branches: []const Block,
        explicit_join: bool,
        is_parallel: bool = false,
    },
    using_expr: struct {
        span: Span,
        target: *const Expr,
        instances: []const []const Span,
    },
    todo_expr: struct {
        span: Span,
        message: ?*const Expr,
    },
    panic_expr: struct {
        span: Span,
        message: ?*const Expr,
    },
    err: Span,

    pub fn getSpan(self: Expr) Span {
        return switch (self) {
            .int_lit => |s| s,
            .float_lit => |s| s,
            .string_lit => |s| s,
            .bool_lit => |v| v.span,
            .ident => |s| s,
            .upper_ident => |s| s,
            .placeholder => |s| s,
            .unary => |v| v.span,
            .binary => |v| v.span,
            .cast => |v| v.span,
            .call => |v| v.span,
            .field => |v| v.span,
            .index => |v| v.span,
            .try_op => |v| v.span,
            .record_lit => |v| v.span,
            .tuple => |v| v.span,
            .list => |v| v.span,
            .block => |b| b.span,
            .if_expr => |v| v.span,
            .case_expr => |v| v.span,
            .lambda => |v| v.span,
            .view_expr => |v| v.span,
            .fork_expr => |v| v.span,
            .using_expr => |v| v.span,
            .todo_expr => |v| v.span,
            .panic_expr => |v| v.span,
            .err => |s| s,
        };
    }
};

pub const Stmt = union(enum) {
    let_stmt: struct {
        span: Span,
        attrs: []const Attribute,
        mutable: bool,
        pattern: *const Pattern,
        ty: ?*const TypeExpr,
        value: *const Expr,
    },
    use_stmt: struct {
        span: Span,
        patterns: []const *const Pattern,
        expr: *const Expr,
    },
    assign_stmt: struct {
        span: Span,
        target: *const Expr,
        op: AssignOp,
        value: *const Expr,
    },
    return_stmt: struct {
        span: Span,
        value: ?*const Expr,
    },
    while_stmt: struct {
        span: Span,
        cond: *const Expr,
        decreases: ?*const Expr,
        body: Block,
    },
    for_stmt: struct {
        span: Span,
        pattern: *const Pattern,
        iter: *const Expr,
        decreases: ?*const Expr,
        body: Block,
    },
    expr_stmt: struct {
        span: Span,
        attrs: []const Attribute,
        expr: *const Expr,
        has_semi: bool,
    },

    pub fn getSpan(self: Stmt) Span {
        return switch (self) {
            .let_stmt => |v| v.span,
            .use_stmt => |v| v.span,
            .assign_stmt => |v| v.span,
            .return_stmt => |v| v.span,
            .while_stmt => |v| v.span,
            .for_stmt => |v| v.span,
            .expr_stmt => |v| v.span,
        };
    }
};

pub const RecordField = struct {
    span: Span,
    doc_comments: []const Span,
    attrs: []const Attribute,
    is_pub: bool,
    mutable: bool,
    name: Span,
    ty: *const TypeExpr,
};

pub const VariantField = struct {
    span: Span,
    label: ?Span,
    mutable: bool,
    ty: *const TypeExpr,
};

pub const Variant = struct {
    span: Span,
    doc_comments: []const Span,
    attrs: []const Attribute,
    name: Span,
    fields: []const VariantField,
};

pub const TypeBody = union(enum) {
    empty,
    alias: *const TypeExpr,
    record: []const RecordField,
    variants: []const Variant,
};

pub const LawClause = union(enum) {
    preserves: struct {
        span: Span,
        paths: []const FieldPath,
    },
    when: struct {
        span: Span,
        expr: *const Expr,
    },
    always: struct {
        span: Span,
        expr: *const Expr,
    },
    never: struct {
        span: Span,
        expr: *const Expr,
    },
    expr: struct {
        span: Span,
        expr: *const Expr,
    },
};

pub const ExternFn = struct {
    span: Span,
    doc_comments: []const Span,
    attrs: []const Attribute,
    is_pub: bool,
    name: Span,
    params: []const Param,
    ret: ?*const TypeExpr,
};

pub const Decl = struct {
    span: Span,
    doc_comments: []const Span,
    attrs: []const Attribute,
    is_pub: bool,
    kind: Kind,

    pub const Kind = union(enum) {
        import_decl: struct {
            path: []const Span,
            alias: ?Span,
            members: []const Span,
        },
        type_decl: struct {
            is_opaque: bool,
            name: Span,
            type_params: []const Span,
            constraints: []const TraitConstraint = &.{},
            body: TypeBody,
        },
        fn_decl: struct {
            name: Span,
            params: []const Param,
            ret: ?*const TypeExpr,
            decreases: ?*const Expr,
            constraints: []const TraitConstraint = &.{},
            has_body: bool = true,
            body: Block,
        },
        trait_decl: struct {
            name: Span,
            params: []const TraitParam,
            supers: []const TraitConstraint,
            methods: []const TraitMethodSig,
            laws: []const TraitLaw,
        },
        instance_decl: struct {
            is_default: bool,
            name: ?Span,
            trait_ref: TraitConstraint,
            constraints: []const TraitConstraint,
            methods: []const InstanceMethod,
        },
        const_decl: struct {
            name: Span,
            ty: ?*const TypeExpr,
            value: *const Expr,
        },
        law_decl: struct {
            name: Span,
            params: []const Param,
            clauses: []const LawClause,
        },
        extern_decl: struct {
            abi: Span,
            fns: []const ExternFn,
        },
    };
};

pub const Module = struct {
    doc_comments: []const Span,
    decls: []const Decl,
};

pub const Ast = struct {
    arena: std.heap.ArenaAllocator,
    source: [:0]const u8,
    tokens: []const lexer.Token,
    module: Module,
    diagnostics: []const Diagnostic,

    pub fn deinit(self: *Ast) void {
        self.arena.deinit();
    }

    pub fn hasErrors(self: *const Ast) bool {
        return self.diagnostics.len > 0;
    }
};

pub fn formatAst(ast: *const Ast, writer: *Io.Writer) Io.Writer.Error!void {
    try writer.writeAll("(module");
    if (ast.module.doc_comments.len > 0) {
        try writer.print(" (docs {d})", .{ast.module.doc_comments.len});
    }
    for (ast.module.decls) |decl| {
        try writer.writeByte('\n');
        try formatDecl(ast.source, &decl, 1, writer);
    }
    try writer.writeAll(")\n");
}

fn writeIndent(writer: *Io.Writer, depth: usize) Io.Writer.Error!void {
    var i: usize = 0;
    while (i < depth) : (i += 1) {
        try writer.writeAll("  ");
    }
}

fn formatPath(source: []const u8, path: []const Span, sep: []const u8, writer: *Io.Writer) Io.Writer.Error!void {
    for (path, 0..) |seg, i| {
        if (i > 0) try writer.writeAll(sep);
        try writer.writeAll(seg.slice(source));
    }
}

fn formatAttributes(source: []const u8, attrs: []const Attribute, writer: *Io.Writer) Io.Writer.Error!void {
    for (attrs) |attr| {
        try writer.print(" (@{s}", .{attr.name.slice(source)});
        switch (attr.payload) {
            .none => {},
            .layout => |spec| {
                try writer.writeAll(" ");
                switch (spec) {
                    .aos => try writer.writeAll("aos"),
                    .soa => try writer.writeAll("soa"),
                    .aosoa => |tile| {
                        try writer.writeAll("(aosoa");
                        if (tile) |tile_expr| {
                            try writer.writeByte(' ');
                            try formatExpr(source, tile_expr, 0, writer);
                        }
                        try writer.writeByte(')');
                    },
                    .auto => try writer.writeAll("auto"),
                    .@"packed" => try writer.writeAll("packed"),
                    .flat => try writer.writeAll("flat"),
                }
            },
            .args => |args| {
                for (args) |arg| {
                    try writer.writeByte(' ');
                    try formatExpr(source, arg, 0, writer);
                }
            },
        }
        try writer.writeByte(')');
    }
}

fn formatParams(source: []const u8, params: []const Param, writer: *Io.Writer) Io.Writer.Error!void {
    try writer.writeAll("(params");
    for (params) |p| {
        try writer.writeAll(" (");
        if (p.label) |lbl| {
            try writer.print("{s}: ", .{lbl.slice(source)});
        }
        if (p.mutable) try writer.writeAll("mut ");
        try writer.writeAll(p.name.slice(source));
        if (p.ty) |ty| {
            try writer.writeAll(" : ");
            try formatType(source, ty, writer);
        }
        try writer.writeByte(')');
    }
    try writer.writeByte(')');
}

fn formatDecl(source: []const u8, decl: *const Decl, depth: usize, writer: *Io.Writer) Io.Writer.Error!void {
    try writeIndent(writer, depth);
    switch (decl.kind) {
        .import_decl => |imp| {
            try writer.writeAll("(import");
            if (decl.is_pub) try writer.writeAll(" pub");
            try writer.writeByte(' ');
            try formatPath(source, imp.path, "/", writer);
            if (imp.alias) |al| {
                try writer.print(" as {s}", .{al.slice(source)});
            }
            if (imp.members.len > 0) {
                try writer.writeAll(" .{");
                try formatPath(source, imp.members, ", ", writer);
                try writer.writeByte('}');
            }
            try writer.writeByte(')');
        },
        .type_decl => |td| {
            try writer.writeAll("(type");
            if (decl.is_pub) try writer.writeAll(" pub");
            if (td.is_opaque) try writer.writeAll(" opaque");
            try formatAttributes(source, decl.attrs, writer);
            try writer.print(" {s}", .{td.name.slice(source)});
            if (td.type_params.len > 0) {
                try writer.writeByte('(');
                try formatPath(source, td.type_params, ", ", writer);
                try writer.writeByte(')');
            }
            switch (td.body) {
                .empty => try writer.writeAll(" opaque_or_empty"),
                .alias => |ty| {
                    try writer.writeAll(" = ");
                    try formatType(source, ty, writer);
                },
                .record => |fields| {
                    try writer.writeAll(" (record");
                    for (fields) |f| {
                        try writer.writeByte('\n');
                        try writeIndent(writer, depth + 1);
                        try writer.writeAll("(field");
                        if (f.is_pub) try writer.writeAll(" pub");
                        if (f.mutable) try writer.writeAll(" mut");
                        try formatAttributes(source, f.attrs, writer);
                        try writer.print(" {s} : ", .{f.name.slice(source)});
                        try formatType(source, f.ty, writer);
                        try writer.writeByte(')');
                    }
                    try writer.writeByte(')');
                },
                .variants => |variants| {
                    try writer.writeAll(" (variants");
                    for (variants) |v| {
                        try writer.writeByte('\n');
                        try writeIndent(writer, depth + 1);
                        try writer.print("({s}", .{v.name.slice(source)});
                        for (v.fields) |vf| {
                            try writer.writeByte(' ');
                            if (vf.label) |lbl| {
                                try writer.print("{s}: ", .{lbl.slice(source)});
                            }
                            if (vf.mutable) try writer.writeAll("mut ");
                            try formatType(source, vf.ty, writer);
                        }
                        try writer.writeByte(')');
                    }
                    try writer.writeByte(')');
                },
            }
            try writer.writeByte(')');
        },
        .fn_decl => |f| {
            try writer.writeAll("(fn");
            if (decl.is_pub) try writer.writeAll(" pub");
            try formatAttributes(source, decl.attrs, writer);
            try writer.print(" {s} ", .{f.name.slice(source)});
            try formatParams(source, f.params, writer);
            if (f.ret) |ret| {
                try writer.writeAll(" -> ");
                try formatType(source, ret, writer);
            }
            if (f.decreases) |dec| {
                try writer.writeAll(" (decreases ");
                try formatExpr(source, dec, depth + 1, writer);
                try writer.writeByte(')');
            }
            if (f.constraints.len > 0) {
                try writer.writeAll(" (with");
                for (f.constraints) |c| {
                    try writer.writeByte(' ');
                    try formatPath(source, c.path, ".", writer);
                }
                try writer.writeByte(')');
            }
            if (f.has_body) {
                try writer.writeByte('\n');
                try writeIndent(writer, depth + 1);
                try formatBlock(source, &f.body, depth + 1, writer);
            } else {
                try writer.writeAll(" (external_decl)");
            }
            try writer.writeByte(')');
        },
        .trait_decl => |tr| {
            try writer.writeAll("(trait");
            if (decl.is_pub) try writer.writeAll(" pub");
            try writer.print(" {s}", .{tr.name.slice(source)});
            for (tr.methods) |m| {
                try writer.writeByte('\n');
                try writeIndent(writer, depth + 1);
                try writer.print("(method {s} ", .{m.name.slice(source)});
                try formatParams(source, m.params, writer);
                if (m.ret) |ret| {
                    try writer.writeAll(" -> ");
                    try formatType(source, ret, writer);
                }
                try writer.writeByte(')');
            }
            try writer.writeByte(')');
        },
        .instance_decl => |inst| {
            try writer.writeAll("(instance");
            if (decl.is_pub) try writer.writeAll(" pub");
            if (inst.is_default) try writer.writeAll(" default");
            if (inst.name) |nm| try writer.print(" {s}:", .{nm.slice(source)});
            try writer.writeByte(' ');
            try formatPath(source, inst.trait_ref.path, ".", writer);
            for (inst.methods) |m| {
                try writer.writeByte('\n');
                try writeIndent(writer, depth + 1);
                try writer.print("(method {s} ", .{m.name.slice(source)});
                try formatParams(source, m.params, writer);
                try writer.writeByte(')');
            }
            try writer.writeByte(')');
        },
        .const_decl => |c| {
            try writer.writeAll("(const");
            if (decl.is_pub) try writer.writeAll(" pub");
            try formatAttributes(source, decl.attrs, writer);
            try writer.print(" {s}", .{c.name.slice(source)});
            if (c.ty) |ty| {
                try writer.writeAll(" : ");
                try formatType(source, ty, writer);
            }
            try writer.writeByte(' ');
            try formatExpr(source, c.value, depth + 1, writer);
            try writer.writeByte(')');
        },
        .law_decl => |l| {
            try writer.writeAll("(law");
            if (decl.is_pub) try writer.writeAll(" pub");
            try formatAttributes(source, decl.attrs, writer);
            try writer.print(" {s} ", .{l.name.slice(source)});
            try formatParams(source, l.params, writer);
            for (l.clauses) |cl| {
                try writer.writeByte('\n');
                try writeIndent(writer, depth + 1);
                switch (cl) {
                    .preserves => |p| {
                        try writer.writeAll("(preserves");
                        for (p.paths) |path| {
                            try writer.writeByte(' ');
                            try formatPath(source, path, ".", writer);
                        }
                        try writer.writeByte(')');
                    },
                    .when => |w| {
                        try writer.writeAll("(when ");
                        try formatExpr(source, w.expr, depth + 1, writer);
                        try writer.writeByte(')');
                    },
                    .always => |a| {
                        try writer.writeAll("(always ");
                        try formatExpr(source, a.expr, depth + 1, writer);
                        try writer.writeByte(')');
                    },
                    .never => |n| {
                        try writer.writeAll("(never ");
                        try formatExpr(source, n.expr, depth + 1, writer);
                        try writer.writeByte(')');
                    },
                    .expr => |e| {
                        try writer.writeAll("(assert ");
                        try formatExpr(source, e.expr, depth + 1, writer);
                        try writer.writeByte(')');
                    },
                }
            }
            try writer.writeByte(')');
        },
        .extern_decl => |ex| {
            try writer.writeAll("(extern");
            if (decl.is_pub) try writer.writeAll(" pub");
            try formatAttributes(source, decl.attrs, writer);
            try writer.print(" {s}", .{ex.abi.slice(source)});
            for (ex.fns) |ef| {
                try writer.writeByte('\n');
                try writeIndent(writer, depth + 1);
                try writer.writeAll("(extern_fn");
                if (ef.is_pub) try writer.writeAll(" pub");
                try writer.print(" {s} ", .{ef.name.slice(source)});
                try formatParams(source, ef.params, writer);
                if (ef.ret) |ret| {
                    try writer.writeAll(" -> ");
                    try formatType(source, ret, writer);
                }
                try writer.writeByte(')');
            }
            try writer.writeByte(')');
        },
    }
}

pub fn formatType(source: []const u8, ty: *const TypeExpr, writer: *Io.Writer) Io.Writer.Error!void {
    switch (ty.*) {
        .primitive => |p| switch (p.prim) {
            .unsigned => |bits| try writer.print("u{d}", .{bits}),
            .signed => |bits| try writer.print("i{d}", .{bits}),
            .f32 => try writer.writeAll("f32"),
            .f64 => try writer.writeAll("f64"),
            .bool => try writer.writeAll("bool"),
        },
        .int_range => |ir| {
            try writer.writeAll("(IntRange ");
            try formatExpr(source, ir.lo, 0, writer);
            try writer.writeAll(if (ir.inclusive) " ..= " else " .. ");
            try formatExpr(source, ir.hi, 0, writer);
            try writer.writeByte(')');
        },
        .named => |n| {
            if (n.args.len > 0) try writer.writeByte('(');
            try formatPath(source, n.path, ".", writer);
            for (n.args) |arg| {
                try writer.writeByte(' ');
                try formatType(source, arg, writer);
            }
            if (n.args.len > 0) try writer.writeByte(')');
        },
        .type_var => |tv| try writer.writeAll(tv.name.slice(source)),
        .path_borrow => |pb| {
            try writer.writeAll("(~> ");
            try formatType(source, pb.base, writer);
            if (pb.borrow.mode) |m| {
                try writer.print(" {s}", .{@tagName(m)});
            }
            try writer.writeAll(" .{");
            for (pb.borrow.paths, 0..) |path, i| {
                if (i > 0) try writer.writeAll(", ");
                try formatPath(source, path, ".", writer);
            }
            try writer.writeAll("})");
        },
        .fn_type => |ft| {
            try writer.writeAll(if (ft.is_once) "(once fn (" else "(fn (");
            for (ft.params, 0..) |p, i| {
                if (i > 0) try writer.writeByte(' ');
                try formatType(source, p, writer);
            }
            try writer.writeAll(") -> ");
            try formatType(source, ft.ret, writer);
            try writer.writeByte(')');
        },
        .tuple => |tp| {
            try writer.writeAll("(tuple");
            for (tp.elems) |el| {
                try writer.writeByte(' ');
                try formatType(source, el, writer);
            }
            try writer.writeByte(')');
        },
        .slice => |sl| {
            try writer.writeAll(if (sl.mutable) "[mut " else "[");
            try formatType(source, sl.elem, writer);
            try writer.writeByte(']');
        },
        .inferred => try writer.writeByte('_'),
    }
}

pub fn formatPattern(source: []const u8, pat: *const Pattern, writer: *Io.Writer) Io.Writer.Error!void {
    switch (pat.*) {
        .wildcard => try writer.writeByte('_'),
        .ident => |id| {
            if (id.mutable) try writer.writeAll("(mut ");
            try writer.writeAll(id.name.slice(source));
            if (id.mutable) try writer.writeByte(')');
        },
        .literal => |lit| {
            if (lit.negative) try writer.writeByte('-');
            try writer.writeAll(lit.tok.loc.slice(source));
        },
        .range => |rg| {
            try writer.writeByte('(');
            try writer.writeAll(if (rg.inclusive) "..=" else "..");
            try writer.writeByte(' ');
            try formatPattern(source, rg.lo, writer);
            try writer.writeByte(' ');
            try formatPattern(source, rg.hi, writer);
            try writer.writeByte(')');
        },
        .tuple => |tp| {
            try writer.writeAll("(tup");
            for (tp.elems) |el| {
                try writer.writeByte(' ');
                try formatPattern(source, el, writer);
            }
            try writer.writeByte(')');
        },
        .list => |ls| {
            try writer.writeAll("(list");
            for (ls.elems) |el| {
                try writer.writeByte(' ');
                try formatPattern(source, el, writer);
            }
            if (ls.rest) |rest| {
                try writer.print(" ..{s}", .{rest.slice(source)});
            }
            try writer.writeByte(')');
        },
        .constructor => |ctor| {
            try writer.writeAll("(ctor ");
            try formatPath(source, ctor.path, ".", writer);
            for (ctor.args) |arg| {
                try writer.writeByte(' ');
                if (arg.label) |lbl| try writer.print("{s}:", .{lbl.slice(source)});
                try formatPattern(source, arg.pattern, writer);
            }
            if (ctor.has_rest) try writer.writeAll(" ..");
            try writer.writeByte(')');
        },
        .alias => |al| {
            try writer.writeAll("(as ");
            try formatPattern(source, al.inner, writer);
            try writer.print(" {s})", .{al.name.slice(source)});
        },
        .or_pat => |op| {
            try writer.writeAll("(or");
            for (op.alternatives) |alt| {
                try writer.writeByte(' ');
                try formatPattern(source, alt, writer);
            }
            try writer.writeByte(')');
        },
    }
}

pub fn formatBlock(source: []const u8, blk: *const Block, depth: usize, writer: *Io.Writer) Io.Writer.Error!void {
    try writer.writeAll("(block");
    try formatAttributes(source, blk.attrs, writer);
    for (blk.stmts) |st| {
        try writer.writeByte('\n');
        try writeIndent(writer, depth + 1);
        try formatStmt(source, &st, depth + 1, writer);
    }
    if (blk.tail) |tail| {
        try writer.writeByte('\n');
        try writeIndent(writer, depth + 1);
        try writer.writeAll("(tail ");
        try formatExpr(source, tail, depth + 1, writer);
        try writer.writeByte(')');
    }
    try writer.writeByte(')');
}

fn formatStmt(source: []const u8, stmt: *const Stmt, depth: usize, writer: *Io.Writer) Io.Writer.Error!void {
    switch (stmt.*) {
        .let_stmt => |ls| {
            try writer.writeAll("(let");
            if (ls.mutable) try writer.writeAll(" mut");
            try formatAttributes(source, ls.attrs, writer);
            try writer.writeByte(' ');
            try formatPattern(source, ls.pattern, writer);
            if (ls.ty) |ty| {
                try writer.writeAll(" : ");
                try formatType(source, ty, writer);
            }
            try writer.writeByte(' ');
            try formatExpr(source, ls.value, depth, writer);
            try writer.writeByte(')');
        },
        .use_stmt => |us| {
            try writer.writeAll("(use (");
            for (us.patterns, 0..) |pat, i| {
                if (i > 0) try writer.writeByte(' ');
                try formatPattern(source, pat, writer);
            }
            try writer.writeAll(") ");
            try formatExpr(source, us.expr, depth, writer);
            try writer.writeByte(')');
        },
        .assign_stmt => |asg| {
            try writer.print("({s} ", .{asg.op.symbol()});
            try formatExpr(source, asg.target, depth, writer);
            try writer.writeByte(' ');
            try formatExpr(source, asg.value, depth, writer);
            try writer.writeByte(')');
        },
        .return_stmt => |rs| {
            try writer.writeAll("(return");
            if (rs.value) |v| {
                try writer.writeByte(' ');
                try formatExpr(source, v, depth, writer);
            }
            try writer.writeByte(')');
        },
        .while_stmt => |ws| {
            try writer.writeAll("(while ");
            try formatExpr(source, ws.cond, depth, writer);
            if (ws.decreases) |dec| {
                try writer.writeAll(" (decreases ");
                try formatExpr(source, dec, depth, writer);
                try writer.writeByte(')');
            }
            try writer.writeByte(' ');
            try formatBlock(source, &ws.body, depth, writer);
            try writer.writeByte(')');
        },
        .for_stmt => |fs| {
            try writer.writeAll("(for ");
            try formatPattern(source, fs.pattern, writer);
            try writer.writeByte(' ');
            try formatExpr(source, fs.iter, depth, writer);
            if (fs.decreases) |dec| {
                try writer.writeAll(" (decreases ");
                try formatExpr(source, dec, depth, writer);
                try writer.writeByte(')');
            }
            try writer.writeByte(' ');
            try formatBlock(source, &fs.body, depth, writer);
            try writer.writeByte(')');
        },
        .expr_stmt => |es| {
            try writer.writeAll("(stmt");
            try formatAttributes(source, es.attrs, writer);
            try writer.writeByte(' ');
            try formatExpr(source, es.expr, depth, writer);
            try writer.writeByte(')');
        },
    }
}

pub fn formatExpr(source: []const u8, expr: *const Expr, depth: usize, writer: *Io.Writer) Io.Writer.Error!void {
    switch (expr.*) {
        .int_lit => |s| try writer.writeAll(s.slice(source)),
        .float_lit => |s| try writer.writeAll(s.slice(source)),
        .string_lit => |s| try writer.writeAll(s.slice(source)),
        .bool_lit => |b| try writer.writeAll(if (b.value) "true" else "false"),
        .ident => |s| try writer.writeAll(s.slice(source)),
        .upper_ident => |s| try writer.writeAll(s.slice(source)),
        .placeholder => try writer.writeByte('_'),
        .unary => |u| {
            try writer.print("({s} ", .{u.op.symbol()});
            try formatExpr(source, u.operand, depth, writer);
            try writer.writeByte(')');
        },
        .binary => |b| {
            try writer.print("({s} ", .{b.op.symbol()});
            try formatExpr(source, b.left, depth, writer);
            try writer.writeByte(' ');
            try formatExpr(source, b.right, depth, writer);
            try writer.writeByte(')');
        },
        .cast => |c| {
            try writer.writeAll("(as ");
            try formatExpr(source, c.expr, depth, writer);
            try writer.writeByte(' ');
            try formatType(source, c.ty, writer);
            try writer.writeByte(')');
        },
        .call => |c| {
            try writer.writeAll("(call ");
            try formatExpr(source, c.callee, depth, writer);
            for (c.args) |arg| {
                try writer.writeByte(' ');
                if (arg.label) |lbl| {
                    try writer.print("{s}:", .{lbl.slice(source)});
                }
                try formatExpr(source, arg.value, depth, writer);
            }
            try writer.writeByte(')');
        },
        .field => |f| {
            try writer.writeAll("(. ");
            try formatExpr(source, f.target, depth, writer);
            try writer.print(" {s})", .{f.name.slice(source)});
        },
        .index => |ix| {
            try writer.writeAll("([] ");
            try formatExpr(source, ix.target, depth, writer);
            try writer.writeByte(' ');
            try formatExpr(source, ix.idx, depth, writer);
            try writer.writeByte(')');
        },
        .try_op => |t| {
            try writer.writeAll("(? ");
            try formatExpr(source, t.operand, depth, writer);
            try writer.writeByte(')');
        },
        .record_lit => |rl| {
            try writer.writeAll("(record_lit ");
            try formatPath(source, rl.path, ".", writer);
            for (rl.fields) |rf| {
                try writer.print(" {s}", .{rf.name.slice(source)});
                if (rf.value) |v| {
                    try writer.writeByte(':');
                    try formatExpr(source, v, depth, writer);
                }
            }
            try writer.writeByte(')');
        },
        .tuple => |tp| {
            try writer.writeAll("(tup");
            for (tp.elems) |el| {
                try writer.writeByte(' ');
                try formatExpr(source, el, depth, writer);
            }
            try writer.writeByte(')');
        },
        .list => |ls| {
            try writer.writeAll("(list");
            for (ls.elems) |el| {
                try writer.writeByte(' ');
                try formatExpr(source, el, depth, writer);
            }
            try writer.writeByte(')');
        },
        .block => |*blk| try formatBlock(source, blk, depth, writer),
        .if_expr => |ie| {
            try writer.writeAll("(if ");
            try formatExpr(source, ie.cond, depth, writer);
            try writer.writeByte(' ');
            try formatBlock(source, &ie.then_block, depth, writer);
            if (ie.else_branch) |eb| {
                try writer.writeByte(' ');
                try formatExpr(source, eb, depth, writer);
            }
            try writer.writeByte(')');
        },
        .case_expr => |ce| {
            try writer.writeAll("(case (");
            for (ce.subjects, 0..) |subj, i| {
                if (i > 0) try writer.writeByte(' ');
                try formatExpr(source, subj, depth, writer);
            }
            try writer.writeByte(')');
            for (ce.arms) |arm| {
                try writer.writeAll(" (arm (");
                for (arm.alternatives, 0..) |alt, j| {
                    if (j > 0) try writer.writeAll(" | ");
                    try writer.writeByte('(');
                    for (alt, 0..) |pat, k| {
                        if (k > 0) try writer.writeByte(' ');
                        try formatPattern(source, pat, writer);
                    }
                    try writer.writeByte(')');
                }
                try writer.writeByte(')');
                if (arm.guard) |g| {
                    try writer.writeAll(" (if ");
                    try formatExpr(source, g, depth, writer);
                    try writer.writeByte(')');
                }
                try writer.writeByte(' ');
                try formatExpr(source, arm.body, depth, writer);
                try writer.writeByte(')');
            }
            try writer.writeByte(')');
        },
        .lambda => |lam| {
            try writer.writeAll(if (lam.is_once) "(once fn " else "(fn ");
            try formatParams(source, lam.params, writer);
            if (lam.ret) |ret| {
                try writer.writeAll(" -> ");
                try formatType(source, ret, writer);
            }
            try writer.writeByte(' ');
            try formatBlock(source, &lam.body, depth, writer);
            try writer.writeByte(')');
        },
        .view_expr => |vw| {
            try writer.writeAll("(view");
            if (vw.mode) |m| try writer.print(" {s}", .{@tagName(m)});
            if (vw.binding) |b| try writer.print(" {s} =", .{b.slice(source)});
            try writer.writeByte(' ');
            try formatExpr(source, vw.target, depth, writer);
            try writer.writeByte(' ');
            try formatBlock(source, &vw.body, depth, writer);
            try writer.writeByte(')');
        },
        .fork_expr => |fk| {
            try writer.writeAll("(fork");
            if (fk.is_parallel) try writer.writeAll(" parallel");
            if (fk.explicit_join) try writer.writeAll(" join");
            for (fk.branches) |*br| {
                try writer.writeByte(' ');
                try formatBlock(source, br, depth, writer);
            }
            try writer.writeByte(')');
        },
        .using_expr => |ue| {
            try writer.writeAll("(using ");
            try formatExpr(source, ue.target, depth, writer);
            for (ue.instances) |inst_path| {
                try writer.writeByte(' ');
                try formatPath(source, inst_path, ".", writer);
            }
            try writer.writeByte(')');
        },
        .todo_expr => |td| {
            try writer.writeAll("(todo");
            if (td.message) |m| {
                try writer.writeByte(' ');
                try formatExpr(source, m, depth, writer);
            }
            try writer.writeByte(')');
        },
        .panic_expr => |pn| {
            try writer.writeAll("(panic");
            if (pn.message) |m| {
                try writer.writeByte(' ');
                try formatExpr(source, m, depth, writer);
            }
            try writer.writeByte(')');
        },
        .err => try writer.writeAll("<err>"),
    }
}
