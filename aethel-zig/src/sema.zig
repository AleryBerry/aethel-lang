const std = @import("std");
const lexer = @import("lexer.zig");
const ast = @import("ast.zig");
const int_range = @import("int_range.zig");
const layout = @import("layout.zig");
const law_verifier = @import("law_verifier.zig");

pub const IntType = int_range.IntType;
pub const IntRange = int_range.IntRange;

pub const SemaDiagnostic = struct {
    span: ast.Span,
    kind: Kind,
    message: []const u8,

    pub const Kind = enum {
        duplicate_decl,
        unknown_type,
        unknown_ident,
        type_mismatch,
        literal_out_of_range,
        potential_overflow,
        width_exceeded,
        invalid_int_range,
        use_after_move,
        mutability_error,
        unauthorized_field_access,
        borrow_conflict,
        fork_data_race,
        invalid_ffi_type,
        law_violation,
        invalid_layout,
        affine_capture,
        termination_error,
    };
};

pub const Ty = union(enum) {
    int: IntType,
    int_range: struct {
        range: IntRange,
        synthesized: IntType,
    },
    f32,
    f64,
    bool,
    string,
    unit,
    record: usize,
    adt: usize,
    opaque_ty: usize,
    collection: struct {
        elem_record: ?usize,
        elem_ty: *const Ty,
    },
    view: struct {
        mode: ast.BorrowMode,
        target: *const Ty,
        target_record: ?usize,
    },
    path_borrow: struct {
        base: *const Ty,
        mode: ?ast.BorrowMode,
        paths: []const ast.FieldPath,
    },
    slice: struct {
        mutable: bool,
        elem: *const Ty,
    },
    tuple: []const *const Ty,
    fn_ty: struct {
        params: []const *const Ty,
        ret: *const Ty,
        is_once: bool = false,
    },
    option: *const Ty,
    result: struct {
        ok: *const Ty,
        err: *const Ty,
    },
    type_var: []const u8,
    err,

    pub fn isCopyable(self: Ty) bool {
        return switch (self) {
            .int, .int_range, .f32, .f64, .bool, .unit, .type_var, .err => true,
            .string => true,
            .opaque_ty, .collection, .view, .path_borrow, .slice => false,
            .record, .adt => true,
            .tuple => |elems| blk: {
                for (elems) |el| {
                    if (!el.isCopyable()) break :blk false;
                }
                break :blk true;
            },
            .option => |inner| inner.isCopyable(),
            .result => |res| res.ok.isCopyable() and res.err.isCopyable(),
            .fn_ty => |ft| !ft.is_once,
        };
    }

    pub fn isInteger(self: Ty) ?IntType {
        return switch (self) {
            .int => |t| t,
            .int_range => |ir| ir.synthesized,
            else => null,
        };
    }

    pub fn rangeOf(self: Ty) ?IntRange {
        return switch (self) {
            .int => |t| IntRange.ofType(t),
            .int_range => |ir| ir.range,
            else => null,
        };
    }

    pub fn eql(a: Ty, b: Ty) bool {
        if (@intFromEnum(a) != @intFromEnum(b)) return false;
        return switch (a) {
            .int => |ia| ia.signed == b.int.signed and ia.bits == b.int.bits,
            .int_range => |ra| {
                const rb = b.int_range;
                return ra.synthesized.bits == rb.synthesized.bits and
                    ra.synthesized.signed == rb.synthesized.signed and
                    ra.range.containsRange(rb.range) and rb.range.containsRange(ra.range);
            },
            .f32, .f64, .bool, .string, .unit, .err => true,
            .record => |id| id == b.record,
            .adt => |id| id == b.adt,
            .opaque_ty => |id| id == b.opaque_ty,
            .type_var => |n| std.mem.eql(u8, n, b.type_var),
            .option => |inner| inner.eql(b.option.*),
            .slice => |sa| sa.mutable == b.slice.mutable and sa.elem.eql(b.slice.elem.*),
            .collection => |ca| ca.elem_ty.eql(b.collection.elem_ty.*),
            .view => |va| va.mode == b.view.mode and va.target.eql(b.view.target.*),
            .path_borrow => |pa| pa.base.eql(b.path_borrow.base.*),
            .result => |ra| ra.ok.eql(b.result.ok.*) and ra.err.eql(b.result.err.*),
            .tuple => |ta| blk: {
                if (ta.len != b.tuple.len) break :blk false;
                for (ta, b.tuple) |ea, eb| {
                    if (!ea.eql(eb.*)) break :blk false;
                }
                break :blk true;
            },
            .fn_ty => |fa| blk: {
                if (fa.is_once != b.fn_ty.is_once) break :blk false;
                if (fa.params.len != b.fn_ty.params.len) break :blk false;
                if (!fa.ret.eql(b.fn_ty.ret.*)) break :blk false;
                for (fa.params, b.fn_ty.params) |pa, pb| {
                    if (!pa.eql(pb.*)) break :blk false;
                }
                break :blk true;
            },
        };
    }
};

pub const CheckedField = struct {
    name: []const u8,
    ty: *const Ty,
    bits: u16,
    signed: bool,
    mutable: bool,
};

pub const CheckedRecord = struct {
    name: []const u8,
    span: ast.Span,
    fields: []const CheckedField,
    conflicts: []const layout.ConflictPair,
    record_layout: layout.RecordLayout,
    collection_layout: ?layout.CollectionLayout,
    hot_fields: []const bool = &.{},
    auto_layout_decision: ?layout.AutoLayoutDecision = null,
};

pub const CheckedADTVariant = struct {
    name: []const u8,
    field_types: []const *const Ty,
    field_labels: []const ?[]const u8,
};

pub const CheckedADT = struct {
    name: []const u8,
    span: ast.Span,
    variant_names: []const []const u8,
    variants: []const CheckedADTVariant,
    adt_layout: layout.CompactADTLayout,
};

pub const CheckedCollection = struct {
    name: []const u8,
    layout: layout.CollectionLayout,
    field_count: usize,
};

pub const FieldAccessEffect = struct {
    record_idx: usize,
    field_idx: usize,
};

pub const BorrowPerm = enum {
    shared,
    reserved,
    active_exclusive,
    frozen,

    pub fn compatible(a: BorrowPerm, b: BorrowPerm) bool {
        return switch (a) {
            .shared => b == .shared or b == .frozen or b == .reserved,
            .frozen => b == .shared or b == .frozen or b == .reserved,
            .reserved => b == .shared or b == .frozen,
            .active_exclusive => false,
        };
    }

    pub fn mirName(self: BorrowPerm) []const u8 {
        return switch (self) {
            .shared => "shared",
            .reserved => "reserved",
            .active_exclusive => "exclusive",
            .frozen => "frozen",
        };
    }
};

pub const PermTraceOp = union(enum) {
    reserve: struct {
        view_id: usize,
        root_name: []const u8,
        record_idx: usize,
        field_idx: ?usize,
        perm: BorrowPerm,
    },
    activate: struct {
        view_id: usize,
    },
    freeze: struct {
        view_id: usize,
    },
    read: struct {
        view_id: usize,
    },
    write: struct {
        view_id: usize,
        val: u8,
    },
    release: struct {
        view_id: usize,
    },
};

pub const AffineForm = struct {
    base: ?[]const u8 = null,
    base_version: u32 = 0,
    base_nonneg: bool = false,
    offset: i64 = 0,

    pub fn eqlVar(a: AffineForm, b: AffineForm) bool {
        if (a.base == null and b.base == null) return true;
        if (a.base != null and b.base != null) {
            return std.mem.eql(u8, a.base.?, b.base.?) and a.base_version == b.base_version;
        }
        return false;
    }

    pub fn isPureNat(self: AffineForm) bool {
        if (self.offset < 0) return false;
        if (self.base != null and !self.base_nonneg) return false;
        return true;
    }
};

pub const SymbolicSlice = struct {
    lo: AffineForm,
    hi: AffineForm,
};

pub const AccessIndex = union(enum) {
    elem: AffineForm,
    slice: SymbolicSlice,
    unknown,
};

pub const OrderFact = struct {
    lhs: AffineForm,
    rhs: AffineForm,
    kind: Kind,

    pub const Kind = enum { ne, lt, le };
};

pub const DisjointCertEmit = struct {
    facts: []const OrderFact,
    kind: Kind,

    pub const Kind = union(enum) {
        idx_ne: struct { a: AffineForm, b: AffineForm },
        slice_disjoint: struct { s1: SymbolicSlice, s2: SymbolicSlice },
    };
};

pub const CheckedFunction = struct {
    name: []const u8,
    span: ast.Span,
    type_params: []const []const u8 = &.{},
    param_types: []const *const Ty,
    ret_type: *const Ty,
    reads: []const FieldAccessEffect,
    writes: []const FieldAccessEffect,
    preserves: []const usize,
    target_record: ?usize,
    has_extern_abi: bool,
    perm_trace: []const PermTraceOp,
    disjoint_certs: []const DisjointCertEmit,
    decreases_certs: []const law_verifier.DecreasesCertEmit = &.{},
    returned_origin: ?usize,
};

pub const LawVerdict = enum {
    proved_tier0,
    proved_tier1_exhaustive,
    proved_tier2_symbolic,
    proved_interval,
    proved_tier3_lean,
    falsified,
    unverified_symbolic,
    violated,
};

pub const CheckedLaw = struct {
    name: []const u8,
    span: ast.Span,
    verdict: LawVerdict,
    tier_detail: []const u8 = "",
    counterexample: ?[]const u8 = null,
    symbolic_certs: []const law_verifier.SymbolicLawCert = &.{},
};

pub const CheckedModule = struct {
    arena: std.heap.ArenaAllocator,
    source: [:0]const u8,
    records: []const CheckedRecord,
    adts: []const CheckedADT,
    collections: []const CheckedCollection,
    functions: []const CheckedFunction,
    laws: []const CheckedLaw,
    diagnostics: []const SemaDiagnostic,
    expr_types: std.AutoHashMapUnmanaged(*const ast.Expr, *const Ty),
    let_types: std.AutoHashMapUnmanaged(usize, *const Ty),
    const_types: std.StringHashMapUnmanaged(*const Ty),
    call_type_args: std.AutoHashMapUnmanaged(*const ast.Expr, []const *const Ty),

    pub fn deinit(self: *CheckedModule) void {
        self.arena.deinit();
    }

    pub fn hasErrors(self: *const CheckedModule) bool {
        return self.diagnostics.len > 0;
    }

    pub fn exprType(self: *const CheckedModule, expr: *const ast.Expr) ?*const Ty {
        return self.expr_types.get(expr);
    }

    pub fn letType(self: *const CheckedModule, span_start: usize) ?*const Ty {
        return self.let_types.get(span_start);
    }

    pub fn constType(self: *const CheckedModule, name: []const u8) ?*const Ty {
        return self.const_types.get(name);
    }

    pub fn callTypeArgs(self: *const CheckedModule, expr: *const ast.Expr) ?[]const *const Ty {
        return self.call_type_args.get(expr);
    }
};

const ParamFieldEffect = struct {
    param_idx: usize,
    record_idx: usize,
    field_idx: usize,
};

const CallLink = struct {
    caller_param: usize,
    callee_idx: usize,
    callee_param: usize,
};

const FnSig = struct {
    name: []const u8,
    span: ast.Span,
    type_params: []const []const u8 = &.{},
    params: []const *const Ty,
    param_auths: []const ?[]const usize,
    ret: *const Ty,
    target_record: ?usize,
    is_extern: bool,
    decl_index: ?usize,
    param_reads: std.ArrayList(ParamFieldEffect) = .empty,
    param_writes: std.ArrayList(ParamFieldEffect) = .empty,
    call_links: std.ArrayList(CallLink) = .empty,
    returned_origin: ?usize = null,
};

const ConstEntry = struct {
    name: []const u8,
    ty: *const Ty,
    range: ?IntRange,
};

const Binding = struct {
    name: []const u8,
    ty: *const Ty,
    range: ?IntRange,
    mutable: bool,
    moved: bool,
    authorized_paths: ?[]const usize,
    decl_span: ast.Span,
    ssa_version: u32 = 0,
    is_param: bool = false,
    param_index: ?usize = null,
    view_id: ?usize = null,
    view_root: ?[]const u8 = null,
    view_record_idx: ?usize = null,
    view_field_idx: ?usize = null,
    view_index_key: ?AccessIndex = null,
    view_is_caller_rooted: bool = false,
};

const ActiveView = struct {
    id: usize,
    binding_name: ?[]const u8,
    root_name: []const u8,
    record_idx: ?usize,
    field_idx: ?usize,
    index_key: ?AccessIndex,
    perm: BorrowPerm,
    active: bool = true,
    is_sentinel: bool = false,
    in_trace: bool = false,
};

const AccessRecord = struct {
    root_name: []const u8,
    record_idx: ?usize,
    field_idx: ?usize,
    index_key: ?AccessIndex = null,
    is_write: bool,
    span: ast.Span,
};

const ExprResult = struct {
    ty: *const Ty,
    range: ?IntRange,
    unsized_literal: ?struct { negative: bool, mag: u128 } = null,
};

const Analyzer = struct {
    alloc: std.mem.Allocator,
    source: [:0]const u8,
    module: *const ast.Module,
    diagnostics: *std.ArrayList(SemaDiagnostic),

    record_defs: std.ArrayList(RecordDef),
    adt_defs: std.ArrayList(ADTDef),
    opaque_names: std.ArrayList([]const u8),
    type_aliases: std.StringHashMapUnmanaged(*const Ty),
    fn_sigs: std.ArrayList(FnSig),
    const_map: std.StringHashMapUnmanaged(ConstEntry),

    scopes: std.ArrayList(Binding),
    scope_marks: std.ArrayList(usize),
    active_views: std.ArrayList(ActiveView),
    view_marks: std.ArrayList(usize),
    order_facts: std.ArrayList(OrderFact),
    order_fact_marks: std.ArrayList(usize),
    current_accesses: ?*std.ArrayList(AccessRecord),
    current_perm_trace: ?*std.ArrayList(PermTraceOp),
    current_disjoint_certs: ?*std.ArrayList(DisjointCertEmit),
    next_view_id: usize = 0,
    branch_depth: usize = 0,
    suppress_index_access: bool = false,
    in_projection_base: bool = false,
    active_fork_start: ?usize = null,

    checked_collections: std.ArrayList(CheckedCollection),
    checked_functions: std.ArrayList(CheckedFunction),
    checked_laws: std.ArrayList(CheckedLaw),

    expr_types: std.AutoHashMapUnmanaged(*const ast.Expr, *const Ty),
    let_types: std.AutoHashMapUnmanaged(usize, *const Ty),
    const_types: std.StringHashMapUnmanaged(*const Ty),
    call_type_args: std.AutoHashMapUnmanaged(*const ast.Expr, []const *const Ty) = .empty,
    current_fn_ret: ?*const Ty,
    inferred_return_origin: ?usize = null,
    current_decreases_certs: ?*std.ArrayList(law_verifier.DecreasesCertEmit) = null,
    current_fn_name: ?[]const u8 = null,
    current_fn_params: []const []const u8 = &.{},
    current_fn_decreases: ?*const ast.Expr = null,
    current_sym_guards: std.ArrayList(*const ast.Expr) = .empty,

    const RecordDef = struct {
        name: []const u8,
        span: ast.Span,
        fields: []CheckedField,
        conflicts: std.ArrayList(layout.ConflictPair),
        collection_layout: ?layout.CollectionLayout,
        decl_ast: ast.Decl.Kind,
        auto_layout_requested: bool = false,
        simd_loop_seen: bool = false,
        hot_fields: []bool = &.{},
        observed_collection_len: ?usize = null,
    };

    const ADTDef = struct {
        name: []const u8,
        span: ast.Span,
        variants: []VariantInfo,
        max_payload_bits: u16,
    };

    const VariantInfo = struct {
        name: []const u8,
        field_types: []*const Ty,
        field_labels: []?[]const u8,
    };

    fn addError(self: *Analyzer, kind: SemaDiagnostic.Kind, span: ast.Span, msg: []const u8) void {
        self.diagnostics.append(self.alloc, .{
            .span = span,
            .kind = kind,
            .message = msg,
        }) catch {};
    }

    fn allocTy(self: *Analyzer, ty: Ty) std.mem.Allocator.Error!*const Ty {
        const ptr = try self.alloc.create(Ty);
        ptr.* = ty;
        return ptr;
    }

    fn findRecordIndex(self: *const Analyzer, name: []const u8) ?usize {
        for (self.record_defs.items, 0..) |r, idx| {
            if (std.mem.eql(u8, r.name, name)) return idx;
        }
        return null;
    }

    fn findADTIndex(self: *const Analyzer, name: []const u8) ?usize {
        for (self.adt_defs.items, 0..) |a, idx| {
            if (std.mem.eql(u8, a.name, name)) return idx;
        }
        return null;
    }

    fn findOpaqueIndex(self: *const Analyzer, name: []const u8) ?usize {
        for (self.opaque_names.items, 0..) |n, idx| {
            if (std.mem.eql(u8, n, name)) return idx;
        }
        return null;
    }

    fn findFnIndex(self: *const Analyzer, name: []const u8) ?usize {
        for (self.fn_sigs.items, 0..) |f, idx| {
            if (std.mem.eql(u8, f.name, name)) return idx;
        }
        return null;
    }

    fn lookupVar(self: *Analyzer, name: []const u8) ?*Binding {
        var i = self.scopes.items.len;
        while (i > 0) {
            i -= 1;
            if (std.mem.eql(u8, self.scopes.items[i].name, name)) {
                return &self.scopes.items[i];
            }
        }
        return null;
    }

    fn pushScope(self: *Analyzer) std.mem.Allocator.Error!void {
        try self.scope_marks.append(self.alloc, self.scopes.items.len);
        try self.view_marks.append(self.alloc, self.active_views.items.len);
        try self.order_fact_marks.append(self.alloc, self.order_facts.items.len);
    }

    fn popScope(self: *Analyzer) void {
        if (self.scope_marks.pop()) |mark| {
            self.scopes.shrinkRetainingCapacity(mark);
        }
        if (self.view_marks.pop()) |vmark| {
            if (self.current_perm_trace) |pt| {
                var i = self.active_views.items.len;
                while (i > vmark) {
                    i -= 1;
                    const av = &self.active_views.items[i];
                    if (av.active and av.in_trace) {
                        pt.append(self.alloc, .{ .release = .{ .view_id = av.id } }) catch {};
                    }
                }
            }
            self.active_views.shrinkRetainingCapacity(vmark);
        }
        if (self.order_fact_marks.pop()) |fmark| {
            self.order_facts.shrinkRetainingCapacity(fmark);
        }
    }

    fn registerTypeNames(self: *Analyzer) std.mem.Allocator.Error!void {
        for (self.module.decls) |decl| {
            switch (decl.kind) {
                .type_decl => |td| {
                    const name = td.name.slice(self.source);
                    if (self.findRecordIndex(name) != null or
                        self.findADTIndex(name) != null or
                        self.findOpaqueIndex(name) != null or
                        self.type_aliases.contains(name))
                    {
                        self.addError(.duplicate_decl, td.name, "duplicate type declaration");
                        continue;
                    }
                    switch (td.body) {
                        .empty => {
                            try self.opaque_names.append(self.alloc, name);
                        },
                        .alias => {
                            const err_ty = try self.allocTy(.err);
                            try self.type_aliases.put(self.alloc, name, err_ty);
                        },
                        .record => |fields| {
                            var col_lay: ?layout.CollectionLayout = null;
                            var auto_req = false;
                            for (decl.attrs) |attr| {
                                if (attr.payload == .layout) {
                                    if (attr.payload.layout == .auto) {
                                        auto_req = true;
                                    } else {
                                        col_lay = try self.resolveLayoutAttr(attr.span, attr.payload.layout);
                                    }
                                }
                            }
                            const fslice = try self.alloc.alloc(CheckedField, fields.len);
                            const hslice = try self.alloc.alloc(bool, fields.len);
                            @memset(hslice, false);
                            try self.record_defs.append(self.alloc, .{
                                .name = name,
                                .span = decl.span,
                                .fields = fslice,
                                .conflicts = .empty,
                                .collection_layout = col_lay,
                                .decl_ast = decl.kind,
                                .auto_layout_requested = auto_req,
                                .hot_fields = hslice,
                            });
                        },
                        .variants => |variants| {
                            const vslice = try self.alloc.alloc(VariantInfo, variants.len);
                            try self.adt_defs.append(self.alloc, .{
                                .name = name,
                                .span = decl.span,
                                .variants = vslice,
                                .max_payload_bits = 0,
                            });
                        },
                    }
                },
                else => {},
            }
        }
    }

    fn resolveLayoutAttr(self: *Analyzer, span: ast.Span, spec: ast.LayoutSpec) std.mem.Allocator.Error!?layout.CollectionLayout {
        return switch (spec) {
            .aos => .aos,
            .soa => .soa,
            .auto, .@"packed" => null,
            .aosoa => |tile_expr| blk: {
                var width: usize = 8;
                if (tile_expr) |te| {
                    if (evalConstInt(self.source, te)) |v| {
                        if (v <= 0) {
                            self.addError(.invalid_layout, span, "@layout(aosoa) tile width must be positive (> 0)");
                            break :blk null;
                        }
                        width = @intCast(v);
                    } else {
                        self.addError(.invalid_layout, span, "@layout(aosoa) requires a constant positive integer tile width");
                        break :blk null;
                    }
                }
                break :blk .{ .aosoa = width };
            },
        };
    }

    fn collectTypeVars(self: *Analyzer, ty: *const Ty, list: *std.ArrayList([]const u8)) std.mem.Allocator.Error!void {
        switch (ty.*) {
            .type_var => |tv| {
                for (list.items) |existing| {
                    if (std.mem.eql(u8, existing, tv)) return;
                }
                try list.append(self.alloc, tv);
            },
            .option => |inner| try self.collectTypeVars(inner, list),
            .result => |res| {
                try self.collectTypeVars(res.ok, list);
                try self.collectTypeVars(res.err, list);
            },
            .slice => |sl| try self.collectTypeVars(sl.elem, list),
            .collection => |c| try self.collectTypeVars(c.elem_ty, list),
            .view => |v| try self.collectTypeVars(v.target, list),
            .path_borrow => |pb| try self.collectTypeVars(pb.base, list),
            .tuple => |elems| for (elems) |el| try self.collectTypeVars(el, list),
            .fn_ty => |ft| {
                for (ft.params) |pt| try self.collectTypeVars(pt, list);
                try self.collectTypeVars(ft.ret, list);
            },
            else => {},
        }
    }

    fn containsUnresolvedTypeVar(ty: *const Ty, subst: *const std.StringHashMapUnmanaged(*const Ty)) bool {
        return switch (ty.*) {
            .type_var => |tv| subst.get(tv) == null,
            .option => |inner| containsUnresolvedTypeVar(inner, subst),
            .result => |res| containsUnresolvedTypeVar(res.ok, subst) or containsUnresolvedTypeVar(res.err, subst),
            .slice => |sl| containsUnresolvedTypeVar(sl.elem, subst),
            .collection => |c| containsUnresolvedTypeVar(c.elem_ty, subst),
            .view => |v| containsUnresolvedTypeVar(v.target, subst),
            .path_borrow => |pb| containsUnresolvedTypeVar(pb.base, subst),
            .tuple => |elems| blk: {
                for (elems) |el| if (containsUnresolvedTypeVar(el, subst)) break :blk true;
                break :blk false;
            },
            .fn_ty => |ft| blk: {
                for (ft.params) |pt| if (containsUnresolvedTypeVar(pt, subst)) break :blk true;
                break :blk containsUnresolvedTypeVar(ft.ret, subst);
            },
            else => false,
        };
    }

    fn unifyType(
        self: *Analyzer,
        formal: *const Ty,
        actual: *const Ty,
        subst: *std.StringHashMapUnmanaged(*const Ty),
    ) std.mem.Allocator.Error!bool {
        if (formal.* == .err or actual.* == .err) return true;
        switch (formal.*) {
            .type_var => |tv| {
                if (subst.get(tv)) |bound| {
                    if (bound.* == .err) {
                        try subst.put(self.alloc, tv, actual);
                        return true;
                    }
                    return bound.eql(actual.*);
                }
                try subst.put(self.alloc, tv, actual);
                return true;
            },
            .option => |fi| {
                if (actual.* != .option) return false;
                if (actual.option.* == .err) return true;
                return try self.unifyType(fi, actual.option, subst);
            },
            .result => |fr| {
                if (actual.* != .result) return false;
                const ok_match = actual.result.ok.* == .err or try self.unifyType(fr.ok, actual.result.ok, subst);
                const err_match = actual.result.err.* == .err or try self.unifyType(fr.err, actual.result.err, subst);
                return ok_match and err_match;
            },
            .slice => |fs| {
                if (actual.* != .slice or fs.mutable != actual.slice.mutable) return false;
                return try self.unifyType(fs.elem, actual.slice.elem, subst);
            },
            .collection => |fc| {
                if (actual.* != .collection) return false;
                return try self.unifyType(fc.elem_ty, actual.collection.elem_ty, subst);
            },
            .view => |fv| {
                if (actual.* == .view) {
                    if (fv.mode == .exclusive and actual.view.mode == .shared) return false;
                    return try self.unifyType(fv.target, actual.view.target, subst);
                }
                if (actual.* == .path_borrow) {
                    return try self.unifyType(fv.target, actual.path_borrow.base, subst);
                }
                return try self.unifyType(fv.target, actual, subst);
            },
            .path_borrow => |fpb| {
                if (actual.* == .path_borrow) {
                    return try self.unifyType(fpb.base, actual.path_borrow.base, subst);
                }
                return try self.unifyType(fpb.base, actual, subst);
            },
            .tuple => |ft| {
                if (actual.* != .tuple or ft.len != actual.tuple.len) return false;
                for (ft, actual.tuple) |fe, ae| {
                    if (!try self.unifyType(fe, ae, subst)) return false;
                }
                return true;
            },
            .fn_ty => |ff| {
                if (actual.* != .fn_ty or ff.params.len != actual.fn_ty.params.len) return false;
                if (actual.fn_ty.is_once and !ff.is_once) return false;
                for (ff.params, actual.fn_ty.params) |fp, ap| {
                    if (!try self.unifyType(fp, ap, subst)) return false;
                }
                return try self.unifyType(ff.ret, actual.fn_ty.ret, subst);
            },
            else => return formal.eql(actual.*),
        }
    }

    fn substituteType(
        self: *Analyzer,
        ty: *const Ty,
        subst: *const std.StringHashMapUnmanaged(*const Ty),
    ) std.mem.Allocator.Error!*const Ty {
        if (subst.count() == 0) return ty;
        switch (ty.*) {
            .type_var => |tv| return subst.get(tv) orelse ty,
            .option => |inner| {
                const sub = try self.substituteType(inner, subst);
                return if (sub == inner) ty else try self.allocTy(.{ .option = sub });
            },
            .result => |res| {
                const sok = try self.substituteType(res.ok, subst);
                const serr = try self.substituteType(res.err, subst);
                return if (sok == res.ok and serr == res.err) ty else try self.allocTy(.{ .result = .{ .ok = sok, .err = serr } });
            },
            .slice => |sl| {
                const sub = try self.substituteType(sl.elem, subst);
                return if (sub == sl.elem) ty else try self.allocTy(.{ .slice = .{ .mutable = sl.mutable, .elem = sub } });
            },
            .collection => |c| {
                const sub = try self.substituteType(c.elem_ty, subst);
                return if (sub == c.elem_ty) ty else try self.allocTy(.{ .collection = .{
                    .elem_record = recordOfType(sub),
                    .elem_ty = sub,
                } });
            },
            .view => |v| {
                const sub = try self.substituteType(v.target, subst);
                return if (sub == v.target) ty else try self.allocTy(.{ .view = .{
                    .mode = v.mode,
                    .target = sub,
                    .target_record = recordOfType(sub),
                } });
            },
            .path_borrow => |pb| {
                const sub = try self.substituteType(pb.base, subst);
                return if (sub == pb.base) ty else try self.allocTy(.{ .path_borrow = .{
                    .base = sub,
                    .mode = pb.mode,
                    .paths = pb.paths,
                } });
            },
            .tuple => |elems| {
                const out = try self.alloc.alloc(*const Ty, elems.len);
                var changed = false;
                for (elems, 0..) |el, i| {
                    out[i] = try self.substituteType(el, subst);
                    if (out[i] != el) changed = true;
                }
                return if (!changed) ty else try self.allocTy(.{ .tuple = out });
            },
            .fn_ty => |ft| {
                const ps = try self.alloc.alloc(*const Ty, ft.params.len);
                var changed = false;
                for (ft.params, 0..) |p, i| {
                    ps[i] = try self.substituteType(p, subst);
                    if (ps[i] != p) changed = true;
                }
                const sret = try self.substituteType(ft.ret, subst);
                if (sret != ft.ret) changed = true;
                return if (!changed) ty else try self.allocTy(.{ .fn_ty = .{ .params = ps, .ret = sret, .is_once = ft.is_once } });
            },
            else => return ty,
        }
    }

    fn resolveAllTypeSignatures(self: *Analyzer) std.mem.Allocator.Error!void {
        // Resolve aliases, record fields, and ADT variants.
        for (self.module.decls) |decl| {
            switch (decl.kind) {
                .type_decl => |td| {
                    const name = td.name.slice(self.source);
                    switch (td.body) {
                        .alias => |ty_ast| {
                            const resolved = try self.resolveType(ty_ast);
                            try self.type_aliases.put(self.alloc, name, resolved);
                        },
                        .record => |fields| {
                            if (self.findRecordIndex(name)) |ridx| {
                                for (fields, 0..) |rf, fi| {
                                    const fty = try self.resolveType(rf.ty);
                                    const info = self.typeBitInfo(fty);
                                    self.record_defs.items[ridx].fields[fi] = .{
                                        .name = rf.name.slice(self.source),
                                        .ty = fty,
                                        .bits = info.bits,
                                        .signed = info.signed,
                                        .mutable = rf.mutable,
                                    };
                                }
                            }
                        },
                        .variants => |variants| {
                            if (self.findADTIndex(name)) |aidx| {
                                var max_pay: u16 = 0;
                                for (variants, 0..) |v, vi| {
                                    const fts = try self.alloc.alloc(*const Ty, v.fields.len);
                                    const flbls = try self.alloc.alloc(?[]const u8, v.fields.len);
                                    var vbits: u16 = 0;
                                    for (v.fields, 0..) |vf, fi| {
                                        const rty = try self.resolveType(vf.ty);
                                        fts[fi] = rty;
                                        flbls[fi] = if (vf.label) |lbl| lbl.slice(self.source) else null;
                                        vbits +|= self.typeBitInfo(rty).bits;
                                    }
                                    if (vbits > max_pay) max_pay = vbits;
                                    self.adt_defs.items[aidx].variants[vi] = .{
                                        .name = v.name.slice(self.source),
                                        .field_types = fts,
                                        .field_labels = flbls,
                                    };
                                }
                                self.adt_defs.items[aidx].max_payload_bits = max_pay;
                            }
                        },
                        .empty => {},
                    }
                },
                else => {},
            }
        }

        // Resolve function & extern signatures.
        for (self.module.decls, 0..) |decl, decl_idx| {
            switch (decl.kind) {
                .fn_decl => |fd| {
                    const name = fd.name.slice(self.source);
                    if (self.findFnIndex(name) != null) {
                        self.addError(.duplicate_decl, fd.name, "duplicate function declaration");
                        continue;
                    }
                    const ptypes = try self.alloc.alloc(*const Ty, fd.params.len);
                    const pauths = try self.alloc.alloc(?[]const usize, fd.params.len);
                    var target_rec: ?usize = null;
                    for (fd.params, 0..) |p, pi| {
                        const rty = if (p.ty) |t| try self.resolveType(t) else try self.allocTy(.err);
                        ptypes[pi] = rty;
                        pauths[pi] = try self.extractAuthorizedPaths(p.span, rty);
                        if (target_rec == null) target_rec = recordOfType(rty);
                    }
                    const rty = if (fd.ret) |rt| try self.resolveType(rt) else try self.allocTy(.unit);
                    var tparams: std.ArrayList([]const u8) = .empty;
                    for (ptypes) |pt| try self.collectTypeVars(pt, &tparams);
                    try self.collectTypeVars(rty, &tparams);
                    try self.fn_sigs.append(self.alloc, .{
                        .name = name,
                        .span = fd.name,
                        .type_params = try tparams.toOwnedSlice(self.alloc),
                        .params = ptypes,
                        .param_auths = pauths,
                        .ret = rty,
                        .target_record = target_rec,
                        .is_extern = false,
                        .decl_index = decl_idx,
                    });
                },
                .extern_decl => |ex| {
                    for (ex.fns) |ef| {
                        const name = ef.name.slice(self.source);
                        if (self.findFnIndex(name) != null) {
                            self.addError(.duplicate_decl, ef.name, "duplicate extern function declaration");
                            continue;
                        }
                        const ptypes = try self.alloc.alloc(*const Ty, ef.params.len);
                        const pauths = try self.alloc.alloc(?[]const usize, ef.params.len);
                        for (ef.params, 0..) |p, pi| {
                            const rty = if (p.ty) |t| try self.resolveType(t) else try self.allocTy(.err);
                            ptypes[pi] = rty;
                            pauths[pi] = null;
                            self.validateRustFFIType(p.span, rty);
                        }
                        const rty = if (ef.ret) |rt| try self.resolveType(rt) else try self.allocTy(.unit);
                        self.validateRustFFIType(ef.span, rty);
                        try self.fn_sigs.append(self.alloc, .{
                            .name = name,
                            .span = ef.name,
                            .params = ptypes,
                            .param_auths = pauths,
                            .ret = rty,
                            .target_record = null,
                            .is_extern = true,
                            .decl_index = null,
                        });
                    }
                },
                else => {},
            }
        }
    }

    fn validateRustFFIType(self: *Analyzer, span: ast.Span, ty: *const Ty) void {
        switch (ty.*) {
            .slice => |sl| {
                const ok = switch (sl.elem.*) {
                    .int => |it| it.bits == 8 or it.bits == 16 or it.bits == 32 or it.bits == 64,
                    .f32, .f64 => true,
                    else => false,
                };
                if (!ok) {
                    self.addError(.invalid_ffi_type, span, "Rust FFI slice requires byte-aligned C-ABI scalar element (u8..u64, i8..i64, f32, f64); sub-byte packed slices are forbidden");
                }
            },
            .int => |it| {
                if (it.bits != 8 and it.bits != 16 and it.bits != 32 and it.bits != 64 and it.bits != 128) {
                    self.addError(.invalid_ffi_type, span, "Rust FFI scalar integer must be ABI byte width (8, 16, 32, 64, or 128 bits)");
                }
            },
            .int_range => {
                self.addError(.invalid_ffi_type, span, "Rust FFI boundary requires explicit fixed-width scalar instead of symbolic Int range");
            },
            else => {},
        }
    }

    fn recordOfType(ty: *const Ty) ?usize {
        return switch (ty.*) {
            .record => |idx| idx,
            .collection => |c| c.elem_record,
            .view => |v| v.target_record orelse recordOfType(v.target),
            .path_borrow => |pb| recordOfType(pb.base),
            else => null,
        };
    }

    fn extractAuthorizedPaths(self: *Analyzer, span: ast.Span, ty: *const Ty) std.mem.Allocator.Error!?[]const usize {
        switch (ty.*) {
            .path_borrow => |pb| {
                const ridx = recordOfType(pb.base) orelse return null;
                const fields = self.record_defs.items[ridx].fields;
                var list: std.ArrayList(usize) = .empty;
                for (pb.paths) |fp| {
                    if (fp.len == 0) continue;
                    const fname = fp[0].slice(self.source);
                    var found: ?usize = null;
                    for (fields, 0..) |f, i| {
                        if (std.mem.eql(u8, f.name, fname)) {
                            found = i;
                            break;
                        }
                    }
                    if (found) |fi| {
                        try list.append(self.alloc, fi);
                    } else {
                        self.addError(.unauthorized_field_access, fp[0], "unknown field in path borrow contract");
                    }
                }
                _ = span;
                return try list.toOwnedSlice(self.alloc);
            },
            else => return null,
        }
    }

    const TypeBitInfo = struct {
        bits: u16,
        signed: bool,
        size: usize,
        alignment: usize,
        packable: bool,
    };

    fn typeBitInfo(self: *const Analyzer, ty: *const Ty) TypeBitInfo {
        switch (ty.*) {
            .int => |it| {
                const slot = layout.naturalSlot(it.bits);
                return .{ .bits = it.bits, .signed = it.signed, .size = slot.size, .alignment = slot.alignment, .packable = it.bits < 8 };
            },
            .int_range => |ir| {
                const slot = layout.naturalSlot(ir.synthesized.bits);
                return .{ .bits = ir.synthesized.bits, .signed = ir.synthesized.signed, .size = slot.size, .alignment = slot.alignment, .packable = ir.synthesized.bits < 8 };
            },
            .bool => {
                const slot = layout.naturalSlot(1);
                return .{ .bits = 1, .signed = false, .size = slot.size, .alignment = slot.alignment, .packable = true };
            },
            .f32 => return .{ .bits = 32, .signed = false, .size = 4, .alignment = 4, .packable = false },
            .f64 => return .{ .bits = 64, .signed = false, .size = 8, .alignment = 8, .packable = false },
            .adt => |aidx| {
                const adt_def = self.adt_defs.items[aidx];
                const adt_lay = layout.planCompactADT(adt_def.variants.len, adt_def.max_payload_bits);
                return .{
                    .bits = @max(@as(u16, 1), adt_lay.total_bits),
                    .signed = false,
                    .size = adt_lay.total_bytes,
                    .alignment = layout.naturalAlignment(adt_lay.total_bytes),
                    .packable = adt_lay.can_share_byte,
                };
            },
            .opaque_ty => return .{ .bits = 64, .signed = false, .size = 8, .alignment = 8, .packable = false },
            .collection, .slice, .string => {
                const slot = layout.naturalSlot(128);
                return .{ .bits = 128, .signed = false, .size = slot.size, .alignment = slot.alignment, .packable = false };
            },
            .record => |ridx| {
                // Leaf integer-compatible size if already planned, else default conservative.
                const rf = self.record_defs.items[ridx].fields;
                var approx: usize = 0;
                for (rf) |f| approx += @max(@as(usize, 1), (f.bits + 7) / 8);
                return .{ .bits = 0, .signed = false, .size = approx, .alignment = 8, .packable = false };
            },
            else => return .{ .bits = 64, .signed = false, .size = 8, .alignment = 8, .packable = false },
        }
    }

    fn resolveType(self: *Analyzer, ty_ast: *const ast.TypeExpr) std.mem.Allocator.Error!*const Ty {
        switch (ty_ast.*) {
            .primitive => |p| return switch (p.prim) {
                .unsigned => |bits| try self.allocTy(.{ .int = .{ .signed = false, .bits = bits } }),
                .signed => |bits| try self.allocTy(.{ .int = .{ .signed = true, .bits = bits } }),
                .f32 => try self.allocTy(.f32),
                .f64 => try self.allocTy(.f64),
                .bool => try self.allocTy(.bool),
            },
            .int_range => |ir| {
                const lo_val = evalConstInt(self.source, ir.lo) orelse {
                    self.addError(.invalid_int_range, ir.span, "Int(...) lower bound must be a compile-time constant integer");
                    return try self.allocTy(.err);
                };
                const raw_hi = evalConstInt(self.source, ir.hi) orelse {
                    self.addError(.invalid_int_range, ir.span, "Int(...) upper bound must be a compile-time constant integer");
                    return try self.allocTy(.err);
                };
                const hi_val: i128 = if (ir.inclusive) raw_hi else raw_hi - 1;
                if (lo_val > hi_val) {
                    self.addError(.invalid_int_range, ir.span, "empty or inverted Int(lo..hi) range");
                    return try self.allocTy(.err);
                }
                const range = IntRange{ .bounded = .{ .lo = lo_val, .hi = hi_val } };
                const synth = int_range.inferIntegerType(range) orelse {
                    self.addError(.width_exceeded, ir.span, "Int range exceeds maximum 65535 bits");
                    return try self.allocTy(.err);
                };
                return try self.allocTy(.{ .int_range = .{ .range = range, .synthesized = synth } });
            },
            .named => |n| {
                if (n.path.len == 0) return try self.allocTy(.err);
                const head_name = n.path[n.path.len - 1].slice(self.source);

                if (std.mem.eql(u8, head_name, "String")) return try self.allocTy(.string);
                if (std.mem.eql(u8, head_name, "Option")) {
                    const elem = if (n.args.len > 0) try self.resolveType(n.args[0]) else try self.allocTy(.err);
                    return try self.allocTy(.{ .option = elem });
                }
                if (std.mem.eql(u8, head_name, "Result")) {
                    const ok_ty = if (n.args.len > 0) try self.resolveType(n.args[0]) else try self.allocTy(.err);
                    const err_ty = if (n.args.len > 1) try self.resolveType(n.args[1]) else try self.allocTy(.err);
                    return try self.allocTy(.{ .result = .{ .ok = ok_ty, .err = err_ty } });
                }
                if (std.mem.eql(u8, head_name, "Collection")) {
                    const elem = if (n.args.len > 0) try self.resolveType(n.args[0]) else try self.allocTy(.err);
                    return try self.allocTy(.{ .collection = .{
                        .elem_record = recordOfType(elem),
                        .elem_ty = elem,
                    } });
                }
                if (std.mem.eql(u8, head_name, "View")) {
                    const target = if (n.args.len > 0) try self.resolveType(n.args[0]) else try self.allocTy(.err);
                    var mode: ast.BorrowMode = .shared;
                    if (n.args.len > 1 and n.args[1].* == .named and n.args[1].named.path.len > 0) {
                        const mstr = n.args[1].named.path[0].slice(self.source);
                        if (std.mem.eql(u8, mstr, "Exclusive")) mode = .exclusive;
                    }
                    return try self.allocTy(.{ .view = .{
                        .mode = mode,
                        .target = target,
                        .target_record = recordOfType(target),
                    } });
                }

                if (self.findRecordIndex(head_name)) |ridx| {
                    return try self.allocTy(.{ .record = ridx });
                }
                if (self.findADTIndex(head_name)) |aidx| {
                    return try self.allocTy(.{ .adt = aidx });
                }
                if (self.findOpaqueIndex(head_name)) |oidx| {
                    return try self.allocTy(.{ .opaque_ty = oidx });
                }
                if (self.type_aliases.get(head_name)) |aliased| {
                    return aliased;
                }
                // External or unresolved generic module path like `m.Vec2`: treat gracefully only if qualified, else report unknown type.
                if (n.path.len == 1) {
                    self.addError(.unknown_type, n.span, "unknown type name");
                    return try self.allocTy(.err);
                }
                return try self.allocTy(.{ .type_var = head_name });
            },
            .type_var => |tv| {
                const name = tv.name.slice(self.source);
                if (self.type_aliases.get(name)) |aliased| return aliased;
                return try self.allocTy(.{ .type_var = name });
            },
            .path_borrow => |pb| {
                const base = try self.resolveType(pb.base);
                return try self.allocTy(.{ .path_borrow = .{
                    .base = base,
                    .mode = pb.borrow.mode,
                    .paths = pb.borrow.paths,
                } });
            },
            .fn_type => |ft| {
                const ps = try self.alloc.alloc(*const Ty, ft.params.len);
                for (ft.params, 0..) |pt, i| {
                    ps[i] = try self.resolveType(pt);
                }
                const ret = try self.resolveType(ft.ret);
                return try self.allocTy(.{ .fn_ty = .{ .params = ps, .ret = ret, .is_once = ft.is_once } });
            },
            .tuple => |tp| {
                if (tp.elems.len == 0) return try self.allocTy(.unit);
                const es = try self.alloc.alloc(*const Ty, tp.elems.len);
                for (tp.elems, 0..) |el, i| {
                    es[i] = try self.resolveType(el);
                }
                return try self.allocTy(.{ .tuple = es });
            },
            .slice => |sl| {
                const el = try self.resolveType(sl.elem);
                return try self.allocTy(.{ .slice = .{ .mutable = sl.mutable, .elem = el } });
            },
            .inferred => return try self.allocTy(.err),
        }
    }

    fn evalConstInt(source: [:0]const u8, expr: *const ast.Expr) ?i128 {
        return switch (expr.*) {
            .int_lit => |sp| blk: {
                const parsed = int_range.parseIntLiteral(sp.slice(source)) orelse break :blk null;
                if (parsed.value > @as(u128, @intCast(std.math.maxInt(i128)))) break :blk null;
                break :blk @intCast(parsed.value);
            },
            .unary => |u| {
                if (u.op == .neg) {
                    if (u.operand.* == .int_lit) {
                        const parsed = int_range.parseIntLiteral(u.operand.int_lit.slice(source)) orelse return null;
                        if (parsed.value == @as(u128, 1) << 127) return std.math.minInt(i128);
                        if (parsed.value > @as(u128, @intCast(std.math.maxInt(i128)))) return null;
                        return -@as(i128, @intCast(parsed.value));
                    }
                    const inner = evalConstInt(source, u.operand) orelse return null;
                    return -inner;
                }
                return null;
            },
            .binary => |b| {
                const l = evalConstInt(source, b.left) orelse return null;
                const r = evalConstInt(source, b.right) orelse return null;
                return switch (b.op) {
                    .add => blk: {
                        const res = @addWithOverflow(l, r);
                        break :blk if (res[1] == 0) res[0] else null;
                    },
                    .sub => blk: {
                        const res = @subWithOverflow(l, r);
                        break :blk if (res[1] == 0) res[0] else null;
                    },
                    .mul => blk: {
                        const res = @mulWithOverflow(l, r);
                        break :blk if (res[1] == 0) res[0] else null;
                    },
                    else => null,
                };
            },
            else => null,
        };
    }

    fn checkConstsAndFunctions(self: *Analyzer) std.mem.Allocator.Error!void {
        for (self.module.decls) |decl| {
            switch (decl.kind) {
                .const_decl => |cd| {
                    try self.pushScope();
                    defer self.popScope();

                    const cname = cd.name.slice(self.source);
                    const expected: ?*const Ty = if (cd.ty) |t| try self.resolveType(t) else null;
                    const res = try self.checkExpr(cd.value, expected);
                    const final_ty = expected orelse try self.finalizeInferredType(cd.value.getSpan(), res);
                    if (expected) |exp| {
                        try self.checkAssignmentValue(decl.span, exp, res);
                    }
                    try self.const_types.put(self.alloc, cname, final_ty);
                    try self.const_map.put(self.alloc, cname, .{
                        .name = cname,
                        .ty = final_ty,
                        .range = res.range,
                    });
                },
                else => {},
            }
        }

        for (self.module.decls) |decl| {
            switch (decl.kind) {
                .fn_decl => {
                    try self.checkFunction(decl.span, decl.kind);
                },
                else => {},
            }
        }
    }

    fn checkFunction(self: *Analyzer, span: ast.Span, fd: ast.Decl.Kind) std.mem.Allocator.Error!void {
        const f = fd.fn_decl;
        const fname = f.name.slice(self.source);
        const fsig_idx = self.findFnIndex(fname) orelse return;
        var fsig = &self.fn_sigs.items[fsig_idx];

        try self.pushScope();
        defer self.popScope();

        for (f.params, 0..) |p, pi| {
            const pty = fsig.params[pi];
            try self.scopes.append(self.alloc, .{
                .name = p.name.slice(self.source),
                .ty = pty,
                .range = pty.rangeOf(),
                .mutable = p.mutable,
                .moved = false,
                .authorized_paths = fsig.param_auths[pi],
                .decl_span = p.span,
                .is_param = true,
                .param_index = pi,
            });
        }

        var accesses: std.ArrayList(AccessRecord) = .empty;
        var perm_trace: std.ArrayList(PermTraceOp) = .empty;
        var disjoint_certs: std.ArrayList(DisjointCertEmit) = .empty;
        var decreases_certs: std.ArrayList(law_verifier.DecreasesCertEmit) = .empty;
        var fn_param_names = try self.alloc.alloc([]const u8, f.params.len);
        for (f.params, 0..) |p, pi| fn_param_names[pi] = p.name.slice(self.source);
        if (f.decreases) |dec| _ = try self.checkExpr(dec, null);

        const prev_acc = self.current_accesses;
        const prev_pt = self.current_perm_trace;
        const prev_dc = self.current_disjoint_certs;
        const prev_dec_certs = self.current_decreases_certs;
        const prev_fn_name = self.current_fn_name;
        const prev_fn_params = self.current_fn_params;
        const prev_fn_dec = self.current_fn_decreases;
        const prev_guard_len = self.current_sym_guards.items.len;
        const prev_ret = self.current_fn_ret;
        const prev_orig = self.inferred_return_origin;
        self.current_accesses = &accesses;
        self.current_perm_trace = &perm_trace;
        self.current_disjoint_certs = &disjoint_certs;
        self.current_decreases_certs = &decreases_certs;
        self.current_fn_name = fname;
        self.current_fn_params = fn_param_names;
        self.current_fn_decreases = f.decreases;
        self.current_fn_ret = fsig.ret;
        self.inferred_return_origin = fsig.returned_origin;
        defer {
            self.current_accesses = prev_acc;
            self.current_perm_trace = prev_pt;
            self.current_disjoint_certs = prev_dc;
            self.current_decreases_certs = prev_dec_certs;
            self.current_fn_name = prev_fn_name;
            self.current_fn_params = prev_fn_params;
            self.current_fn_decreases = prev_fn_dec;
            self.current_sym_guards.shrinkRetainingCapacity(prev_guard_len);
            self.current_fn_ret = prev_ret;
            self.inferred_return_origin = prev_orig;
        }

        const body_res = try self.checkBlock(&f.body, fsig.ret, f.ret != null);
        if (f.ret != null and !fsig.ret.eql(.unit)) {
            if (f.body.tail != null or f.body.stmts.len == 0) {
                try self.checkAssignmentValue(f.body.span, fsig.ret, body_res);
                if (fsig.ret.* == .view) {
                    if (f.body.tail) |tail_expr| {
                        try self.verifyReturnedViewOrigin(tail_expr.getSpan(), tail_expr, fsig.ret.view.mode);
                    }
                }
            }
        }
        if (self.inferred_return_origin != null and fsig.returned_origin == null) {
            fsig.returned_origin = self.inferred_return_origin;
        }

        // Release any lingering function-scope active views before ending the trace.
        if (self.view_marks.items.len > 0) {
            const vmark = self.view_marks.items[self.view_marks.items.len - 1];
            var vi = vmark;
            while (vi < self.active_views.items.len) : (vi += 1) {
                const av = &self.active_views.items[vi];
                if (av.active and av.in_trace) {
                    try perm_trace.append(self.alloc, .{ .release = .{ .view_id = av.id } });
                    av.active = false;
                }
            }
        }

        // Summarize reads/writes on records.
        var reads_list: std.ArrayList(FieldAccessEffect) = .empty;
        var writes_list: std.ArrayList(FieldAccessEffect) = .empty;
        for (accesses.items) |acc| {
            if (acc.record_idx) |ridx| {
                if (acc.field_idx) |fidx| {
                    const eff = FieldAccessEffect{ .record_idx = ridx, .field_idx = fidx };
                    if (acc.is_write) {
                        if (!containsAccess(writes_list.items, eff)) try writes_list.append(self.alloc, eff);
                    } else {
                        if (!containsAccess(reads_list.items, eff)) try reads_list.append(self.alloc, eff);
                    }
                }
            }
        }

        try self.checked_functions.append(self.alloc, .{
            .name = fname,
            .span = span,
            .type_params = fsig.type_params,
            .param_types = fsig.params,
            .ret_type = fsig.ret,
            .reads = try reads_list.toOwnedSlice(self.alloc),
            .writes = try writes_list.toOwnedSlice(self.alloc),
            .preserves = &.{},
            .target_record = fsig.target_record,
            .has_extern_abi = false,
            .perm_trace = try perm_trace.toOwnedSlice(self.alloc),
            .disjoint_certs = try disjoint_certs.toOwnedSlice(self.alloc),
            .decreases_certs = try decreases_certs.toOwnedSlice(self.alloc),
            .returned_origin = fsig.returned_origin,
        });
    }

    fn containsAccess(slice: []const FieldAccessEffect, target: FieldAccessEffect) bool {
        for (slice) |item| {
            if (item.record_idx == target.record_idx and item.field_idx == target.field_idx) return true;
        }
        return false;
    }

    const EarlyReleaseTrigger = struct {
        stmt_idx: usize,
        view_id: usize,
    };

    fn checkBlockWithViewRelease(
        self: *Analyzer,
        blk: *const ast.Block,
        expected: ?*const Ty,
        enforce_tail: bool,
        view_id: ?usize,
        early_release_idx: ?usize,
    ) std.mem.Allocator.Error!ExprResult {
        try self.pushScope();
        defer self.popScope();

        var extra_releases: std.ArrayList(EarlyReleaseTrigger) = .empty;

        for (blk.stmts, 0..) |st, si| {
            const scopes_before = self.scopes.items.len;
            try self.checkStmt(&st);
            if (st == .let_stmt and self.scopes.items.len > scopes_before) {
                const last_b = self.scopes.items[self.scopes.items.len - 1];
                if (last_b.view_id) |ret_vid| {
                    if (self.lastUseStmtAfter(blk, si, last_b.name)) |rel_idx| {
                        try extra_releases.append(self.alloc, .{ .stmt_idx = rel_idx, .view_id = ret_vid });
                    }
                }
            }
            if (view_id != null and early_release_idx != null and si == early_release_idx.?) {
                self.releaseActiveViewById(view_id.?);
            }
            for (extra_releases.items) |trig| {
                if (trig.stmt_idx == si) {
                    self.releaseActiveViewById(trig.view_id);
                }
            }
        }

        if (blk.tail) |tail| {
            const tail_expected = if (enforce_tail) expected else null;
            return try self.checkExpr(tail, tail_expected);
        }
        return .{ .ty = try self.allocTy(.unit), .range = null };
    }

    fn checkBlock(
        self: *Analyzer,
        blk: *const ast.Block,
        expected: ?*const Ty,
        enforce_tail: bool,
    ) std.mem.Allocator.Error!ExprResult {
        return try self.checkBlockWithViewRelease(blk, expected, enforce_tail, null, null);
    }

    fn releaseActiveViewById(self: *Analyzer, vid: usize) void {
        for (self.active_views.items) |*av| {
            if (av.id == vid and av.active) {
                av.active = false;
                if (av.in_trace) {
                    if (self.current_perm_trace) |pt| {
                        pt.append(self.alloc, .{ .release = .{ .view_id = av.id } }) catch {};
                    }
                }
            }
        }
    }

    fn checkStmt(self: *Analyzer, stmt: *const ast.Stmt) std.mem.Allocator.Error!void {
        switch (stmt.*) {
            .let_stmt => |ls| {
                const expected: ?*const Ty = if (ls.ty) |t| try self.resolveType(t) else null;
                const val_res = try self.checkExpr(ls.value, expected);
                const final_ty = expected orelse try self.finalizeInferredType(ls.value.getSpan(), val_res);
                if (expected) |exp| {
                    try self.checkAssignmentValue(ls.span, exp, val_res);
                }
                if (!final_ty.isCopyable() and ls.value.* == .ident) {
                    const src_name = ls.value.ident.slice(self.source);
                    if (self.lookupVar(src_name)) |vb| {
                        vb.moved = true;
                    }
                }
                const is_mut_binding = ls.mutable or (ls.pattern.* == .ident and ls.pattern.ident.mutable);
                const final_range = if (is_mut_binding) final_ty.rangeOf() else (val_res.range orelse final_ty.rangeOf());
                try self.let_types.put(self.alloc, ls.span.start, final_ty);
                if (recordOfType(final_ty)) |ridx| {
                    if (ls.value.* == .list) {
                        const cur = self.record_defs.items[ridx].observed_collection_len;
                        const n = ls.value.list.elems.len;
                        self.record_defs.items[ridx].observed_collection_len = if (cur) |c| @max(c, n) else n;
                    }
                    for (ls.attrs) |attr| {
                        if (attr.payload == .layout) {
                            if (attr.payload.layout == .auto) {
                                self.record_defs.items[ridx].auto_layout_requested = true;
                            } else if (try self.resolveLayoutAttr(attr.span, attr.payload.layout)) |cl| {
                                self.record_defs.items[ridx].collection_layout = cl;
                                if (!self.hasCollectionNamed(self.record_defs.items[ridx].name)) {
                                    try self.checked_collections.append(self.alloc, .{
                                        .name = self.record_defs.items[ridx].name,
                                        .layout = cl,
                                        .field_count = @max(@as(usize, 1), self.record_defs.items[ridx].fields.len),
                                    });
                                }
                            }
                        }
                    }
                }
                const scopes_before = self.scopes.items.len;
                try self.bindPattern(ls.pattern, final_ty, final_range, ls.mutable);
                if (final_ty.* == .view and self.scopes.items.len > scopes_before and ls.pattern.* == .ident) {
                    try self.attachReturnedViewBinding(&self.scopes.items[self.scopes.items.len - 1], ls.value, final_ty.view, ls.span);
                }
            },
            .use_stmt => |us| {
                const rhs_res = try self.checkExpr(us.expr, null);
                for (us.patterns) |pat| {
                    try self.bindPattern(pat, rhs_res.ty, rhs_res.range, false);
                }
            },
            .assign_stmt => |asg| {
                const hinted_ty = self.peekWriteTargetType(asg.target);
                const rhs_res = try self.checkExpr(asg.value, hinted_ty);
                const target_info = try self.checkWriteTarget(asg.target, asg.span);
                try self.expr_types.put(self.alloc, asg.target, target_info.ty);
                if (asg.op == .assign) {
                    try self.checkAssignmentValue(asg.span, target_info.ty, rhs_res);
                } else {
                    const lhs_res = ExprResult{ .ty = target_info.ty, .range = target_info.range };
                    const op_bin: ast.BinaryOp = switch (asg.op) {
                        .add_assign => .add,
                        .sub_assign => .sub,
                        .mul_assign => .mul,
                        .div_assign => .div,
                        .rem_assign => .rem,
                        .assign => .add,
                    };
                    const combined = try self.combineBinary(asg.span, op_bin, lhs_res, rhs_res, target_info.ty);
                    try self.checkAssignmentValue(asg.span, target_info.ty, combined);
                }
            },
            .return_stmt => |rs| {
                if (rs.value) |v| {
                    const rv = try self.checkExpr(v, self.current_fn_ret);
                    if (self.current_fn_ret) |ret_ty| {
                        if (!ret_ty.eql(.unit)) {
                            try self.checkAssignmentValue(rs.span, ret_ty, rv);
                            if (ret_ty.* == .view) {
                                try self.verifyReturnedViewOrigin(rs.span, v, ret_ty.view.mode);
                            }
                        }
                    }
                }
            },
            .while_stmt => |ws| {
                _ = try self.checkExpr(ws.cond, null);
                if (ws.decreases) |dec| {
                    _ = try self.checkExpr(dec, null);
                    try self.verifyWhileDecreasesStmt(ws.span, ws.cond, dec, ws.body);
                }
                const saved_ranges = try self.alloc.alloc(?IntRange, self.scopes.items.len);
                for (self.scopes.items, 0..) |sb, si| saved_ranges[si] = sb.range;
                defer {
                    for (0..saved_ranges.len) |si| {
                        if (si < self.scopes.items.len) self.scopes.items[si].range = saved_ranges[si];
                    }
                }
                {
                    try self.pushScope();
                    defer self.popScope();
                    try self.applyBranchGuard(ws.cond, true);
                    _ = try self.checkBlock(&ws.body, null, false);
                }
            },
            .for_stmt => |fs| {
                const iter_res = try self.checkExpr(fs.iter, null);
                if (fs.decreases) |dec| _ = try self.checkExpr(dec, null);
                try self.pushScope();
                defer self.popScope();
                var elem_range: ?IntRange = null;
                const elem_ty: *const Ty = if (fs.iter.* == .binary and (fs.iter.binary.op == .range or fs.iter.binary.op == .range_eq)) blk: {
                    elem_range = iter_res.range;
                    if (fs.iter.binary.op == .range and elem_range != null and elem_range.? == .bounded) {
                        const b = elem_range.?.bounded;
                        if (b.hi > b.lo) {
                            elem_range = .{ .bounded = .{ .lo = b.lo, .hi = b.hi - 1 } };
                        }
                    }
                    break :blk iter_res.ty;
                } else switch (iter_res.ty.*) {
                    .collection => |c| c.elem_ty,
                    .slice => |s| s.elem,
                    else => try self.allocTy(.{ .int = .{ .signed = false, .bits = 64 } }),
                };
                try self.bindPattern(fs.pattern, elem_ty, elem_range orelse elem_ty.rangeOf(), false);
                const loop_acc_start = if (self.current_accesses) |al| al.items.len else 0;
                for (fs.body.stmts) |st| try self.checkStmt(&st);
                if (fs.body.tail) |tail| _ = try self.checkExpr(tail, null);
                if (iter_res.ty.* == .collection) {
                    if (recordOfType(elem_ty)) |ridx| {
                        self.markHotFieldsSince(ridx, loop_acc_start);
                    }
                }
            },
            .expr_stmt => |es| {
                for (es.attrs) |attr| {
                    if (attr.payload == .layout) {
                        if (attr.payload.layout == .auto) {
                            if (self.findCollectionTargetInExpr(es.expr)) |col_info| {
                                self.record_defs.items[col_info.ridx].auto_layout_requested = true;
                            }
                        } else {
                            const col_lay = try self.resolveLayoutAttr(attr.span, attr.payload.layout);
                            if (col_lay) |cl| {
                                if (self.findCollectionTargetInExpr(es.expr)) |col_info| {
                                    self.record_defs.items[col_info.ridx].collection_layout = cl;
                                    if (!self.hasCollectionNamed(col_info.name)) {
                                        try self.checked_collections.append(self.alloc, .{
                                            .name = col_info.name,
                                            .layout = cl,
                                            .field_count = col_info.field_count,
                                        });
                                    }
                                }
                            }
                        }
                    }
                }
                _ = try self.checkExpr(es.expr, null);
            },
        }
    }

    fn findCollectionTargetInExpr(self: *Analyzer, expr: *const ast.Expr) ?struct { ridx: usize, name: []const u8, field_count: usize } {
        var cur = expr;
        while (true) {
            switch (cur.*) {
                .binary => |b| {
                    if (b.op == .pipe) {
                        cur = b.left;
                        continue;
                    }
                    return null;
                },
                .ident => |sp| {
                    const vname = sp.slice(self.source);
                    if (self.lookupVar(vname)) |vb| {
                        if (recordOfType(vb.ty)) |ridx| {
                            return .{
                                .ridx = ridx,
                                .name = self.record_defs.items[ridx].name,
                                .field_count = @max(@as(usize, 1), self.record_defs.items[ridx].fields.len),
                            };
                        }
                    }
                    return null;
                },
                else => return null,
            }
        }
    }

    fn bindPattern(
        self: *Analyzer,
        pat: *const ast.Pattern,
        ty: *const Ty,
        range: ?IntRange,
        default_mut: bool,
    ) std.mem.Allocator.Error!void {
        switch (pat.*) {
            .wildcard, .literal, .range => {},
            .ident => |id| {
                try self.scopes.append(self.alloc, .{
                    .name = id.name.slice(self.source),
                    .ty = ty,
                    .range = range,
                    .mutable = default_mut or id.mutable,
                    .moved = false,
                    .authorized_paths = null,
                    .decl_span = id.span,
                });
            },
            .alias => |al| {
                try self.bindPattern(al.inner, ty, range, default_mut);
                try self.scopes.append(self.alloc, .{
                    .name = al.name.slice(self.source),
                    .ty = ty,
                    .range = range,
                    .mutable = default_mut,
                    .moved = false,
                    .authorized_paths = null,
                    .decl_span = al.name,
                });
            },
            .tuple => |tp| {
                for (tp.elems, 0..) |el, i| {
                    const ety: *const Ty = if (ty.* == .tuple and i < ty.tuple.len) ty.tuple[i] else ty;
                    try self.bindPattern(el, ety, ety.rangeOf(), default_mut);
                }
            },
            .list => |ls| {
                for (ls.elems) |el| {
                    const ety: *const Ty = if (ty.* == .slice) ty.slice.elem else ty;
                    try self.bindPattern(el, ety, ety.rangeOf(), default_mut);
                }
                if (ls.rest) |rest| {
                    try self.scopes.append(self.alloc, .{
                        .name = rest.slice(self.source),
                        .ty = ty,
                        .range = null,
                        .mutable = default_mut,
                        .moved = false,
                        .authorized_paths = null,
                        .decl_span = rest,
                    });
                }
            },
            .constructor => |ctor| {
                const opt_var = self.lookupConstructorVariant(ctor.path, ty);
                for (ctor.args, 0..) |arg, ai| {
                    const arg_ty: *const Ty = if (opt_var) |vi| blk: {
                        if (arg.label) |lbl| {
                            const lname = lbl.slice(self.source);
                            for (vi.field_labels, 0..) |flbl, fi| {
                                if (flbl != null and std.mem.eql(u8, flbl.?, lname)) {
                                    break :blk vi.field_types[fi];
                                }
                            }
                        }
                        if (ai < vi.field_types.len) break :blk vi.field_types[ai];
                        break :blk try self.allocTy(.err);
                    } else try self.allocTy(.err);
                    try self.bindPattern(arg.pattern, arg_ty, arg_ty.rangeOf(), default_mut);
                }
            },
            .or_pat => |op| {
                if (op.alternatives.len > 0) {
                    try self.bindPattern(op.alternatives[0], ty, range, default_mut);
                }
            },
        }
    }

    const WriteTargetInfo = struct {
        ty: *const Ty,
        range: ?IntRange,
    };

    fn peekWriteTargetType(self: *Analyzer, target: *const ast.Expr) ?*const Ty {
        switch (target.*) {
            .ident => |sp| {
                const vb = self.lookupVar(sp.slice(self.source)) orelse return null;
                return vb.ty;
            },
            .field => |fld| {
                const bt = self.peekWriteTargetType(fld.target) orelse return null;
                const ridx = recordOfType(bt) orelse return null;
                const fidx = self.findRecordField(ridx, fld.name.slice(self.source)) orelse return null;
                return self.record_defs.items[ridx].fields[fidx].ty;
            },
            .index => |ix| {
                const bt = self.peekWriteTargetType(ix.target) orelse return null;
                return switch (bt.*) {
                    .slice => |sl| sl.elem,
                    .collection => |c| c.elem_ty,
                    .view => |v| switch (v.target.*) {
                        .slice => |sl| sl.elem,
                        .collection => |c| c.elem_ty,
                        else => null,
                    },
                    else => null,
                };
            },
            else => return null,
        }
    }

    const ResolvedRoot = struct {
        root_name: ?[]const u8 = null,
        through_view_id: ?usize = null,
        view_index_key: ?AccessIndex = null,
    };

    fn resolveAccessRoot(self: *Analyzer, expr: *const ast.Expr) ResolvedRoot {
        const raw_root = self.extractRootIdent(expr) orelse return .{};
        if (self.lookupVar(raw_root)) |vb| {
            if (vb.view_id != null or vb.view_root != null) {
                return .{
                    .root_name = vb.view_root orelse raw_root,
                    .through_view_id = vb.view_id,
                    .view_index_key = vb.view_index_key,
                };
            }
        }
        return .{ .root_name = raw_root, .through_view_id = null, .view_index_key = null };
    }

    fn checkWriteTarget(self: *Analyzer, target: *const ast.Expr, stmt_span: ast.Span) std.mem.Allocator.Error!WriteTargetInfo {
        switch (target.*) {
            .ident => |sp| {
                const name = sp.slice(self.source);
                const vb = self.lookupVar(name) orelse {
                    self.addError(.unknown_ident, sp, "assignment to undeclared identifier");
                    return .{ .ty = try self.allocTy(.err), .range = null };
                };
                if (vb.moved) {
                    self.addError(.use_after_move, sp, "cannot assign to moved value");
                }
                if (!vb.mutable) {
                    self.addError(.mutability_error, sp, "cannot assign to immutable binding; mark with 'mut'");
                }
                if (self.active_fork_start) |fstart| {
                    if (!self.in_projection_base and vb.decl_span.start < fstart and vb.ty.* != .fn_ty) {
                        try self.recordAccess(name, recordOfType(vb.ty), null, true, stmt_span, null, vb.view_id);
                    }
                }
                // Assigning to an integer/local variable advances its SSA identity for AffineIndex facts.
                vb.ssa_version +|= 1;
                return .{ .ty = vb.ty, .range = vb.range };
            },
            .field => |fld| {
                var base: ExprResult = undefined;
                var idx_key: ?AccessIndex = null;
                var resolved: ResolvedRoot = .{};
                const prev_proj = self.in_projection_base;
                self.in_projection_base = true;
                if (fld.target.* == .index) {
                    const prev_sup = self.suppress_index_access;
                    self.suppress_index_access = true;
                    base = try self.checkExpr(fld.target, null);
                    self.suppress_index_access = prev_sup;
                    self.in_projection_base = prev_proj;
                    resolved = self.resolveAccessRoot(fld.target.index.target);
                    idx_key = resolved.view_index_key orelse self.extractAccessIndex(fld.target.index.idx);
                } else {
                    base = try self.checkExpr(fld.target, null);
                    self.in_projection_base = prev_proj;
                    resolved = self.resolveAccessRoot(fld.target);
                    idx_key = resolved.view_index_key;
                }
                const ridx = recordOfType(base.ty) orelse {
                    return .{ .ty = try self.allocTy(.err), .range = null };
                };
                const fname = fld.name.slice(self.source);
                const fidx = self.findRecordField(ridx, fname) orelse {
                    self.addError(.unknown_ident, fld.name, "unknown field on record");
                    return .{ .ty = try self.allocTy(.err), .range = null };
                };
                // Verify path-borrow authorization (`~>.{...}`) and view write permission.
                if (self.extractRootIdent(fld.target)) |raw_rn| {
                    if (self.lookupVar(raw_rn)) |vb| {
                        if (vb.authorized_paths) |auths| {
                            var allowed = false;
                            for (auths) |ai| {
                                if (ai == fidx) {
                                    allowed = true;
                                    break;
                                }
                            }
                            if (!allowed) {
                                self.addError(.unauthorized_field_access, fld.name, "write violates parameter ~>.{...} path borrow contract");
                            }
                        }
                        if (vb.ty.* == .view and vb.ty.view.mode == .shared) {
                            self.addError(.borrow_conflict, fld.target.getSpan(), "cannot mutate field through a shared view");
                        }
                    }
                }
                if (resolved.root_name) |rn| {
                    try self.recordAccess(rn, ridx, fidx, true, stmt_span, idx_key, resolved.through_view_id);
                }
                const cf = self.record_defs.items[ridx].fields[fidx];
                return .{ .ty = cf.ty, .range = cf.ty.rangeOf() };
            },
            .index => |ix| {
                const prev_proj = self.in_projection_base;
                self.in_projection_base = true;
                const base = try self.checkExpr(ix.target, null);
                self.in_projection_base = false;
                _ = try self.checkExpr(ix.idx, null);
                self.in_projection_base = prev_proj;
                const elem_ty: *const Ty = switch (base.ty.*) {
                    .slice => |sl| sl.elem,
                    .collection => |c| c.elem_ty,
                    .view => |v| switch (v.target.*) {
                        .slice => |sl| sl.elem,
                        .collection => |c| c.elem_ty,
                        else => try self.allocTy(.{ .int = .{ .signed = false, .bits = 8 } }),
                    },
                    else => try self.allocTy(.{ .int = .{ .signed = false, .bits = 8 } }),
                };
                if (self.extractRootIdent(ix.target)) |rn| {
                    if (self.lookupVar(rn)) |vb| {
                        if (vb.ty.* == .view and vb.ty.view.mode == .shared) {
                            self.addError(.borrow_conflict, ix.target.getSpan(), "cannot write through a shared view");
                        } else if (vb.ty.* == .slice and !vb.ty.slice.mutable) {
                            self.addError(.mutability_error, ix.target.getSpan(), "cannot write to immutable slice");
                        }
                    }
                }
                const resolved = self.resolveAccessRoot(ix.target);
                if (resolved.root_name) |rn| {
                    const idx_key = resolved.view_index_key orelse self.extractAccessIndex(ix.idx);
                    try self.recordAccess(rn, recordOfType(elem_ty), null, true, stmt_span, idx_key, resolved.through_view_id);
                }
                return .{ .ty = elem_ty, .range = elem_ty.rangeOf() };
            },
            else => return .{ .ty = try self.allocTy(.err), .range = null },
        }
    }

    fn findRecordField(self: *const Analyzer, ridx: usize, fname: []const u8) ?usize {
        for (self.record_defs.items[ridx].fields, 0..) |f, i| {
            if (std.mem.eql(u8, f.name, fname)) return i;
        }
        return null;
    }

    fn extractRootIdent(self: *const Analyzer, expr: *const ast.Expr) ?[]const u8 {
        var cur = expr;
        while (true) {
            switch (cur.*) {
                .ident => |sp| return sp.slice(self.source),
                .field => |f| cur = f.target,
                .index => |ix| cur = ix.target,
                else => return null,
            }
        }
    }

    fn fieldsMayOverlap(a_field: ?usize, b_field: ?usize) bool {
        return a_field == null or b_field == null or a_field.? == b_field.?;
    }

    fn canActivateView(self: *Analyzer, vid: usize) bool {
        var target_av: ?*const ActiveView = null;
        for (self.active_views.items) |*av| {
            if (av.id == vid) {
                target_av = av;
                break;
            }
        }
        const mine = target_av orelse return true;
        for (self.active_views.items) |other| {
            if (!other.active or other.id == vid) continue;
            if (!std.mem.eql(u8, other.root_name, mine.root_name)) continue;
            if (mine.index_key != null and other.index_key != null) {
                if (self.accessIndicesDisjoint(mine.index_key.?, other.index_key.?, false)) continue;
            }
            if (fieldsMayOverlap(mine.field_idx, other.field_idx)) return false;
        }
        return true;
    }

    fn recordAccess(
        self: *Analyzer,
        root_name: []const u8,
        record_idx: ?usize,
        field_idx: ?usize,
        is_write: bool,
        span: ast.Span,
        index_key: ?AccessIndex,
        through_view_id: ?usize,
    ) std.mem.Allocator.Error!void {
        // 1. Access explicitly routed through a live `View` binding:
        if (through_view_id) |vid| {
            for (self.active_views.items) |*av| {
                if (av.id != vid) continue;
                if (!av.active) {
                    self.addError(.borrow_conflict, span, "view used after release");
                    break;
                }
                if (is_write) {
                    switch (av.perm) {
                        .shared, .frozen => {
                            self.addError(.borrow_conflict, span, "cannot mutate through a shared or frozen view");
                        },
                        .reserved => {
                            if (!self.canActivateView(vid)) {
                                self.addError(.borrow_conflict, span, "cannot activate reserved exclusive view while a conflicting shared view is live");
                            } else {
                                av.perm = .active_exclusive;
                                if (av.in_trace) {
                                    if (self.current_perm_trace) |pt| {
                                        try pt.append(self.alloc, .{ .activate = .{ .view_id = vid } });
                                        try pt.append(self.alloc, .{ .write = .{ .view_id = vid, .val = 1 } });
                                    }
                                }
                            }
                        },
                        .active_exclusive => {
                            if (av.in_trace) {
                                if (self.current_perm_trace) |pt| {
                                    try pt.append(self.alloc, .{ .write = .{ .view_id = vid, .val = 1 } });
                                }
                            }
                        },
                    }
                } else {
                    if (av.in_trace) {
                        if (self.current_perm_trace) |pt| {
                            try pt.append(self.alloc, .{ .read = .{ .view_id = vid } });
                        }
                    }
                }
                break;
            }
        } else {
            // 2. Direct access on raw root `root_name`: check all active overlapping views.
            for (self.active_views.items) |*av| {
                if (!av.active) continue;
                if (!std.mem.eql(u8, av.root_name, root_name)) continue;

                // Disjoint slice / element index proves non-overlap on arrays/collections.
                if (av.index_key != null and index_key != null) {
                    if (self.accessIndicesDisjoint(av.index_key.?, index_key.?, false)) continue;
                }

                const same_field = fieldsMayOverlap(av.field_idx, field_idx);
                if (!same_field) {
                    // Disjoint sibling concurrent exclusive view + access adds co-borrow conflict edge!
                    if ((is_write or av.perm == .reserved or av.perm == .active_exclusive) and record_idx != null and av.field_idx != null and field_idx != null) {
                        try self.addConflictEdge(record_idx.?, av.field_idx.?, field_idx.?);
                    }
                    continue;
                }

                // Legacy lexical guard sentinel view (unused view binding in scope, e.g. `view exclusive va = fl.flag_a`):
                if (av.is_sentinel and av.perm != .shared) {
                    if (is_write and av.perm == .reserved and self.canActivateView(av.id)) {
                        av.perm = .active_exclusive;
                        if (av.in_trace) {
                            if (self.current_perm_trace) |pt| {
                                try pt.append(self.alloc, .{ .activate = .{ .view_id = av.id } });
                                try pt.append(self.alloc, .{ .write = .{ .view_id = av.id, .val = 1 } });
                            }
                        }
                    }
                    continue;
                }

                if (is_write) {
                    if (av.perm == .shared or av.perm == .frozen) {
                        self.addError(.borrow_conflict, span, "cannot mutate path while an active shared view locks it");
                    } else {
                        self.addError(.borrow_conflict, span, "cannot mutate raw path while an exclusive view borrows it");
                    }
                } else {
                    // Shared read of raw root: ALLOWED during `.reserved` (two-phase lazy borrow!),
                    // REJECTED during `.active_exclusive`!
                    if (av.perm == .active_exclusive) {
                        self.addError(.borrow_conflict, span, "cannot read path while an activated exclusive view holds it");
                    } else if (av.perm == .reserved and self.branch_depth == 0 and record_idx != null and self.current_perm_trace != null) {
                        const tmp_id = self.next_view_id;
                        self.next_view_id += 1;
                        try self.current_perm_trace.?.append(self.alloc, .{ .reserve = .{
                            .view_id = tmp_id,
                            .root_name = root_name,
                            .record_idx = record_idx.?,
                            .field_idx = field_idx,
                            .perm = .shared,
                        } });
                        try self.current_perm_trace.?.append(self.alloc, .{ .read = .{ .view_id = tmp_id } });
                        try self.current_perm_trace.?.append(self.alloc, .{ .release = .{ .view_id = tmp_id } });
                    }
                }
            }
        }
        if (self.current_accesses) |acc_list| {
            try acc_list.append(self.alloc, .{
                .root_name = root_name,
                .record_idx = record_idx,
                .field_idx = field_idx,
                .index_key = index_key,
                .is_write = is_write,
                .span = span,
            });
        }
    }

    fn addConflictEdge(self: *Analyzer, ridx: usize, a: usize, b: usize) std.mem.Allocator.Error!void {
        if (a == b) return;
        const list = &self.record_defs.items[ridx].conflicts;
        for (list.items) |edge| {
            if ((edge.a == a and edge.b == b) or (edge.a == b and edge.b == a)) return;
        }
        try list.append(self.alloc, .{ .a = a, .b = b });
    }

    fn finalizeInferredType(self: *Analyzer, span: ast.Span, res: ExprResult) std.mem.Allocator.Error!*const Ty {
        if (res.unsized_literal) |lit| {
            const rng: IntRange = if (lit.negative) blk: {
                if (lit.mag > @as(u128, @intCast(std.math.maxInt(i128)))) {
                    return try self.allocTy(.{ .int = .{ .signed = true, .bits = 129 } });
                }
                break :blk IntRange.singleton(-@as(i128, @intCast(lit.mag)));
            } else blk: {
                if (lit.mag > @as(u128, @intCast(std.math.maxInt(i128)))) {
                    return try self.allocTy(.{ .int = .{ .signed = false, .bits = int_range.minUnsignedBits(lit.mag) } });
                }
                break :blk IntRange.singleton(@intCast(lit.mag));
            };
            const it = int_range.inferIntegerType(rng) orelse {
                self.addError(.width_exceeded, span, "integer literal exceeds maximum 65535 bits");
                return try self.allocTy(.err);
            };
            return try self.allocTy(.{ .int = it });
        }
        if (res.ty.* != .err) return res.ty;
        if (res.range) |rng| {
            const it = int_range.inferIntegerType(rng) orelse {
                self.addError(.width_exceeded, span, "computed integer range exceeds 65535 bits");
                return try self.allocTy(.err);
            };
            return try self.allocTy(.{ .int = it });
        }
        return res.ty;
    }

    fn checkAssignmentValue(self: *Analyzer, span: ast.Span, target: *const Ty, val: ExprResult) std.mem.Allocator.Error!void {
        if (target.* == .err) return;
        if (val.ty.* == .err and val.unsized_literal == null and val.range == null) return;

        // Check unsized integer literal fit directly against target integer / IntRange type.
        if (val.unsized_literal) |lit| {
            switch (target.*) {
                .int => |it| {
                    const ok = if (lit.negative) int_range.fitsSignedNegated(lit.mag, it) else int_range.fitsNonNeg(lit.mag, it);
                    if (!ok) {
                        self.addError(.literal_out_of_range, span, "integer literal out of range for target bit-width type");
                    }
                    return;
                },
                .int_range => |ir| {
                    if (val.range) |lr| {
                        if (!ir.range.containsRange(lr)) {
                            self.addError(.literal_out_of_range, span, "integer literal out of range for Int(lo..hi) bounds");
                        }
                    }
                    return;
                },
                else => {
                    self.addError(.type_mismatch, span, "integer literal assigned to non-integer target type");
                    return;
                },
            }
        }

        // Check range / integer overflow safety!
        switch (target.*) {
            .int => |it| {
                if (val.ty.* == .int_range) {
                    const rng = val.range orelse val.ty.int_range.range;
                    if (!rng.fitsType(it)) {
                        self.addError(.potential_overflow, span, "potential integer overflow: expression range exceeds target integer type");
                    }
                    return;
                }
                if (val.ty.* == .int) {
                    const src_it = val.ty.int;
                    if (src_it.signed != it.signed or src_it.bits != it.bits) {
                        if (val.range) |rng| {
                            if (rng.fitsType(it)) return;
                        }
                        self.addError(.potential_overflow, span, "integer type mismatch or potential overflow into target width");
                    }
                    return;
                }
            },
            .int_range => |ir| {
                if (val.range) |rng| {
                    if (!ir.range.containsRange(rng)) {
                        self.addError(.potential_overflow, span, "potential integer overflow: expression interval may exceed Int(lo..hi) bounds");
                    }
                    return;
                }
                if (val.ty.isInteger()) |src_it| {
                    if (!IntRange.ofType(src_it).fitsType(ir.synthesized) or !ir.range.containsRange(IntRange.ofType(src_it))) {
                        self.addError(.potential_overflow, span, "integer expression may exceed Int(lo..hi) bounds");
                    }
                    return;
                }
            },
            else => {},
        }

        if (target.* == .path_borrow) {
            if (target.path_borrow.base.eql(val.ty.*)) return;
        }
        if (val.ty.* == .path_borrow) {
            if (val.ty.path_borrow.base.eql(target.*)) return;
        }
        if (target.* == .view) {
            const inner_ok = switch (val.ty.*) {
                .view => |vv| blk: {
                    if (target.view.mode == .exclusive and vv.mode == .shared) {
                        self.addError(.borrow_conflict, span, "cannot coerce shared View to Exclusive View");
                    }
                    break :blk target.view.target.eql(vv.target.*);
                },
                .path_borrow => |pb| blk: {
                    if (target.view.mode == .exclusive and pb.mode != null and pb.mode.? == .shared) {
                        self.addError(.borrow_conflict, span, "cannot coerce shared path borrow to Exclusive View");
                    }
                    break :blk target.view.target.eql(pb.base.*);
                },
                else => target.view.target.eql(val.ty.*),
            };
            if (inner_ok) return;
        }
        if (target.* == .option and val.ty.* == .option) {
            if (val.ty.option.* == .err or target.option.* == .err or target.option.eql(val.ty.option.*)) return;
            self.addError(.type_mismatch, span, "Option element type mismatch");
            return;
        }
        if (target.* == .result and val.ty.* == .result) {
            const ok_ok = val.ty.result.ok.* == .err or target.result.ok.* == .err or target.result.ok.eql(val.ty.result.ok.*);
            const err_ok = val.ty.result.err.* == .err or target.result.err.* == .err or target.result.err.eql(val.ty.result.err.*);
            if (ok_ok and err_ok) return;
            self.addError(.type_mismatch, span, "Result payload or error type mismatch");
            return;
        }
        if (target.* == .fn_ty and val.ty.* == .fn_ty) {
            const tf = target.fn_ty;
            const vf = val.ty.fn_ty;
            if (vf.is_once and !tf.is_once) {
                self.addError(.affine_capture, span, "cannot pass affine 'once fn' where reusable 'fn' is expected");
                return;
            }
            if (tf.params.len != vf.params.len or !tf.ret.eql(vf.ret.*)) {
                self.addError(.type_mismatch, span, "function signature mismatch");
                return;
            }
            for (tf.params, vf.params) |tp, vp| {
                if (!tp.eql(vp.*)) {
                    self.addError(.type_mismatch, span, "function parameter type mismatch");
                    return;
                }
            }
            return;
        }
        if (!target.eql(val.ty.*)) {
            self.addError(.type_mismatch, span, "expression type does not match expected type");
        }
    }

    fn checkExpr(self: *Analyzer, expr: *const ast.Expr, expected: ?*const Ty) std.mem.Allocator.Error!ExprResult {
        const res = try self.checkExprInner(expr, expected);
        try self.expr_types.put(self.alloc, expr, res.ty);
        return res;
    }

    fn checkExprInner(self: *Analyzer, expr: *const ast.Expr, expected: ?*const Ty) std.mem.Allocator.Error!ExprResult {
        switch (expr.*) {
            .int_lit => |sp| {
                const parsed = int_range.parseIntLiteral(sp.slice(self.source)) orelse {
                    self.addError(.literal_out_of_range, sp, "integer literal exceeds 128-bit constant parser range");
                    return .{ .ty = try self.allocTy(.err), .range = null };
                };
                if (parsed.suffix) |suf| {
                    if (!int_range.fitsNonNeg(parsed.value, suf)) {
                        self.addError(.literal_out_of_range, sp, "suffixed integer literal out of range for its bit width");
                    }
                    return .{
                        .ty = try self.allocTy(.{ .int = suf }),
                        .range = if (parsed.value <= @as(u128, @intCast(std.math.maxInt(i128)))) IntRange.singleton(@intCast(parsed.value)) else null,
                    };
                }
                const rng: ?IntRange = if (parsed.value <= @as(u128, @intCast(std.math.maxInt(i128))))
                    IntRange.singleton(@intCast(parsed.value))
                else
                    null;
                const inf_ty = if (expected != null and expected.?.isInteger() != null)
                    expected.?
                else if (rng) |r| blk: {
                    const it = int_range.inferIntegerType(r) orelse return .{ .ty = try self.allocTy(.err), .range = null };
                    break :blk try self.allocTy(.{ .int = it });
                } else try self.allocTy(.{ .int = .{ .signed = false, .bits = int_range.minUnsignedBits(parsed.value) } });
                return .{
                    .ty = inf_ty,
                    .range = rng,
                    .unsized_literal = .{ .negative = false, .mag = parsed.value },
                };
            },
            .float_lit => |sp| {
                const raw = sp.slice(self.source);
                const fty: *const Ty = if (std.mem.endsWith(u8, raw, "f32"))
                    try self.allocTy(.f32)
                else if (std.mem.endsWith(u8, raw, "f64"))
                    try self.allocTy(.f64)
                else
                    expected orelse try self.allocTy(.f64);
                return .{ .ty = fty, .range = null };
            },
            .string_lit => return .{ .ty = try self.allocTy(.string), .range = null },
            .bool_lit => return .{ .ty = try self.allocTy(.bool), .range = null },
            .placeholder => return .{ .ty = try self.allocTy(.err), .range = null },
            .ident => |sp| {
                const name = sp.slice(self.source);
                if (self.lookupVar(name)) |vb| {
                    if (vb.moved) {
                        self.addError(.use_after_move, sp, "use of moved affine resource");
                        return .{ .ty = try self.allocTy(.err), .range = null };
                    }
                    if (self.active_fork_start) |fstart| {
                        if (!self.in_projection_base and vb.decl_span.start < fstart and vb.ty.* != .fn_ty) {
                            try self.recordAccess(name, recordOfType(vb.ty), null, false, sp, null, vb.view_id);
                        }
                    }
                    // Implicit affine consumption if value is non-copyable (and not explicitly borrowed via call/field).
                    return .{ .ty = vb.ty, .range = vb.range };
                }
                if (self.const_map.get(name)) |ce| {
                    return .{ .ty = ce.ty, .range = ce.range };
                }
                if (self.findFnIndex(name)) |fidx| {
                    const fs = self.fn_sigs.items[fidx];
                    return .{ .ty = try self.allocTy(.{ .fn_ty = .{ .params = fs.params, .ret = fs.ret } }), .range = null };
                }
                // Check ADT zero-arg constructors if referenced unqualified.
                if (self.lookupADTVariantType(name)) |aty| {
                    return .{ .ty = aty, .range = null };
                }
                self.addError(.unknown_ident, sp, "use of undeclared identifier");
                return .{ .ty = try self.allocTy(.err), .range = null };
            },
            .upper_ident => |sp| {
                const name = sp.slice(self.source);
                if (std.mem.eql(u8, name, "None")) {
                    return .{ .ty = expected orelse try self.allocTy(.{ .option = try self.allocTy(.err) }), .range = null };
                }
                if (self.lookupADTVariantType(name)) |aty| {
                    return .{ .ty = aty, .range = null };
                }
                if (self.findADTIndex(name)) |aidx| {
                    return .{ .ty = try self.allocTy(.{ .adt = aidx }), .range = null };
                }
                return .{ .ty = expected orelse try self.allocTy(.{ .type_var = name }), .range = null };
            },
            .unary => |u| {
                if (u.op == .neg and u.operand.* == .int_lit) {
                    const parsed = int_range.parseIntLiteral(u.operand.int_lit.slice(self.source)) orelse {
                        self.addError(.literal_out_of_range, u.span, "negated integer literal out of range");
                        return .{ .ty = try self.allocTy(.err), .range = null };
                    };
                    if (parsed.suffix) |suf| {
                        if (!int_range.fitsSignedNegated(parsed.value, suf)) {
                            self.addError(.literal_out_of_range, u.span, "negated literal does not fit in its signed bit width");
                        }
                        const neg_rng: ?IntRange = if (parsed.value == @as(u128, 1) << 127)
                            IntRange.singleton(std.math.minInt(i128))
                        else if (parsed.value <= @as(u128, @intCast(std.math.maxInt(i128))))
                            IntRange.singleton(-@as(i128, @intCast(parsed.value)))
                        else
                            null;
                        return .{ .ty = try self.allocTy(.{ .int = suf }), .range = neg_rng };
                    }
                    const neg_rng: ?IntRange = if (parsed.value == @as(u128, 1) << 127)
                        IntRange.singleton(std.math.minInt(i128))
                    else if (parsed.value <= @as(u128, @intCast(std.math.maxInt(i128))))
                        IntRange.singleton(-@as(i128, @intCast(parsed.value)))
                    else
                        null;
                    const ty = if (expected != null and expected.?.isInteger() != null)
                        expected.?
                    else if (neg_rng) |nr| blk: {
                        const it = int_range.inferIntegerType(nr) orelse return .{ .ty = try self.allocTy(.err), .range = null };
                        break :blk try self.allocTy(.{ .int = it });
                    } else try self.allocTy(.err);
                    return .{
                        .ty = ty,
                        .range = neg_rng,
                        .unsized_literal = .{ .negative = true, .mag = parsed.value },
                    };
                }
                if (u.op == .move_op) {
                    const op_res = try self.checkExpr(u.operand, expected);
                    if (u.operand.* == .ident) {
                        const vname = u.operand.ident.slice(self.source);
                        if (self.lookupVar(vname)) |vb| {
                            if (!vb.ty.isCopyable()) {
                                vb.moved = true;
                            }
                        }
                    }
                    return op_res;
                }
                const op_res = try self.checkExpr(u.operand, expected);
                if (u.op == .neg) {
                    const rng = if (op_res.range) |r| r.neg() else null;
                    if (op_res.range != null and rng == null) {
                        self.addError(.width_exceeded, u.span, "negation exceeds supported integer bit width");
                    }
                    const res_ty = if (rng) |nr| blk: {
                        const it = int_range.inferIntegerType(nr) orelse break :blk op_res.ty;
                        break :blk try self.allocTy(.{ .int_range = .{ .range = nr, .synthesized = it } });
                    } else op_res.ty;
                    return .{ .ty = res_ty, .range = rng };
                }
                if (u.op == .not) {
                    return .{ .ty = try self.allocTy(.bool), .range = null };
                }
                return op_res;
            },
            .binary => |b| {
                if (b.op == .pipe) {
                    return try self.checkPipeline(expr, b.left, b.right, expected);
                }
                const lr = try self.checkExpr(b.left, null);
                const rr = try self.checkExpr(b.right, null);
                return try self.combineBinary(b.span, b.op, lr, rr, expected);
            },
            .cast => |c| {
                const target_ty = try self.resolveType(c.ty);
                const inner = try self.checkExpr(c.expr, target_ty);
                try self.checkAssignmentValue(c.span, target_ty, inner);
                return .{ .ty = target_ty, .range = inner.range orelse target_ty.rangeOf() };
            },
            .call => |call_expr| {
                return try self.checkCall(expr, call_expr.span, call_expr.callee, call_expr.args, null, null, expected);
            },
            .field => |fld| {
                var base: ExprResult = undefined;
                var idx_key: ?AccessIndex = null;
                var resolved: ResolvedRoot = .{};
                const prev_proj = self.in_projection_base;
                self.in_projection_base = true;
                if (fld.target.* == .index) {
                    const prev_sup = self.suppress_index_access;
                    self.suppress_index_access = true;
                    base = try self.checkExpr(fld.target, null);
                    self.suppress_index_access = prev_sup;
                    self.in_projection_base = prev_proj;
                    resolved = self.resolveAccessRoot(fld.target.index.target);
                    idx_key = resolved.view_index_key orelse self.extractAccessIndex(fld.target.index.idx);
                } else {
                    base = try self.checkExpr(fld.target, null);
                    self.in_projection_base = prev_proj;
                    resolved = self.resolveAccessRoot(fld.target);
                    idx_key = resolved.view_index_key;
                }
                const fname = fld.name.slice(self.source);
                if (std.mem.eql(u8, fname, "len")) {
                    const is_len_container = switch (base.ty.*) {
                        .slice, .collection, .string => true,
                        .view => |v| v.target.* == .slice or v.target.* == .collection or v.target.* == .string,
                        else => false,
                    };
                    if (is_len_container) {
                        return .{ .ty = try self.allocTy(.{ .int = .{ .signed = false, .bits = 64 } }), .range = null };
                    }
                }
                if (recordOfType(base.ty)) |ridx| {
                    if (self.findRecordField(ridx, fname)) |fidx| {
                        if (resolved.root_name) |rn| {
                            try self.recordAccess(rn, ridx, fidx, false, fld.span, idx_key, resolved.through_view_id);
                        }
                        const cf = self.record_defs.items[ridx].fields[fidx];
                        if (base.ty.* == .collection) {
                            return .{
                                .ty = try self.allocTy(.{ .slice = .{ .mutable = false, .elem = cf.ty } }),
                                .range = null,
                            };
                        }
                        return .{ .ty = cf.ty, .range = cf.ty.rangeOf() };
                    }
                }
                return .{ .ty = try self.allocTy(.err), .range = null };
            },
            .index => |ix| {
                const prev_proj = self.in_projection_base;
                self.in_projection_base = true;
                const base = try self.checkExpr(ix.target, null);
                self.in_projection_base = false;
                if (ix.idx.* == .binary and (ix.idx.binary.op == .range or ix.idx.binary.op == .range_eq)) {
                    _ = try self.checkExpr(ix.idx.binary.left, null);
                    _ = try self.checkExpr(ix.idx.binary.right, null);
                    self.in_projection_base = prev_proj;
                    const elem: *const Ty = switch (base.ty.*) {
                        .slice => |sl| sl.elem,
                        .collection => |c| c.elem_ty,
                        .view => |v| switch (v.target.*) {
                            .slice => |sl| sl.elem,
                            .collection => |c| c.elem_ty,
                            else => try self.allocTy(.{ .int = .{ .signed = false, .bits = 8 } }),
                        },
                        else => try self.allocTy(.{ .int = .{ .signed = false, .bits = 8 } }),
                    };
                    const is_mut = switch (base.ty.*) {
                        .slice => |sl| sl.mutable,
                        .collection => blk: {
                            if (self.extractRootIdent(ix.target)) |rn| {
                                if (self.lookupVar(rn)) |vb| {
                                    if (vb.mutable or vb.authorized_paths != null) break :blk true;
                                }
                            }
                            break :blk false;
                        },
                        .view => |v| v.mode == .exclusive,
                        else => false,
                    };
                    return .{ .ty = try self.allocTy(.{ .slice = .{ .mutable = is_mut, .elem = elem } }), .range = null };
                }
                _ = try self.checkExpr(ix.idx, null);
                self.in_projection_base = prev_proj;
                const elem: *const Ty = switch (base.ty.*) {
                    .slice => |sl| sl.elem,
                    .collection => |c| c.elem_ty,
                    .view => |v| switch (v.target.*) {
                        .slice => |sl| sl.elem,
                        .collection => |c| c.elem_ty,
                        else => try self.allocTy(.{ .int = .{ .signed = false, .bits = 8 } }),
                    },
                    else => try self.allocTy(.{ .int = .{ .signed = false, .bits = 8 } }),
                };
                if (!self.suppress_index_access) {
                    const resolved = self.resolveAccessRoot(ix.target);
                    if (resolved.root_name) |rn| {
                        const idx_key = resolved.view_index_key orelse self.extractAccessIndex(ix.idx);
                        try self.recordAccess(rn, recordOfType(elem), null, false, ix.span, idx_key, resolved.through_view_id);
                    }
                }
                return .{ .ty = elem, .range = elem.rangeOf() };
            },
            .try_op => |t| {
                const inner = try self.checkExpr(t.operand, null);
                return switch (inner.ty.*) {
                    .option => |o| blk: {
                        if (self.current_fn_ret == null or self.current_fn_ret.?.* != .option) {
                            self.addError(.type_mismatch, t.span, "'?' on Option requires enclosing function to return Option(...)");
                        }
                        break :blk .{ .ty = o, .range = o.rangeOf() };
                    },
                    .result => |r| blk: {
                        if (self.current_fn_ret == null or self.current_fn_ret.?.* != .result) {
                            self.addError(.type_mismatch, t.span, "'?' on Result requires enclosing function to return Result(...)");
                        } else if (self.current_fn_ret.?.result.err.* != .err and r.err.* != .err) {
                            try self.checkAssignmentValue(t.span, self.current_fn_ret.?.result.err, .{ .ty = r.err, .range = null });
                        }
                        break :blk .{ .ty = r.ok, .range = r.ok.rangeOf() };
                    },
                    .err => inner,
                    else => blk: {
                        self.addError(.type_mismatch, t.span, "'?' operator requires Option(...) or Result(...) operand");
                        break :blk inner;
                    },
                };
            },
            .record_lit => |rl| {
                const name = if (rl.path.len > 0) rl.path[rl.path.len - 1].slice(self.source) else "";
                if (self.findRecordIndex(name)) |ridx| {
                    const rdef = self.record_defs.items[ridx];
                    for (rl.fields) |rf_init| {
                        const fnm = rf_init.name.slice(self.source);
                        if (self.findRecordField(ridx, fnm)) |fi| {
                            const fty = rdef.fields[fi].ty;
                            if (rf_init.value) |v| {
                                const vr = try self.checkExpr(v, fty);
                                try self.checkAssignmentValue(rf_init.span, fty, vr);
                            }
                        } else {
                            self.addError(.unknown_ident, rf_init.name, "unknown field in record literal");
                        }
                    }
                    return .{ .ty = try self.allocTy(.{ .record = ridx }), .range = null };
                }
                for (rl.fields) |rf_init| {
                    if (rf_init.value) |v| _ = try self.checkExpr(v, null);
                }
                return .{ .ty = try self.allocTy(.err), .range = null };
            },
            .tuple => |tp| {
                if (tp.elems.len == 0) return .{ .ty = try self.allocTy(.unit), .range = null };
                const es = try self.alloc.alloc(*const Ty, tp.elems.len);
                for (tp.elems, 0..) |el, i| {
                    es[i] = (try self.checkExpr(el, null)).ty;
                }
                return .{ .ty = try self.allocTy(.{ .tuple = es }), .range = null };
            },
            .list => |ls| {
                var elem_ty: ?*const Ty = if (expected) |exp| switch (exp.*) {
                    .collection => |c| c.elem_ty,
                    .slice => |s| s.elem,
                    else => null,
                } else null;
                for (ls.elems) |el| {
                    const er = try self.checkExpr(el, elem_ty);
                    if (elem_ty == null) {
                        elem_ty = try self.finalizeInferredType(el.getSpan(), er);
                    } else {
                        try self.checkAssignmentValue(el.getSpan(), elem_ty.?, er);
                    }
                }
                if (expected) |exp| {
                    if (exp.* == .collection) {
                        if (recordOfType(exp)) |ridx| {
                            const cur = self.record_defs.items[ridx].observed_collection_len;
                            self.record_defs.items[ridx].observed_collection_len = if (cur) |c| @max(c, ls.elems.len) else ls.elems.len;
                        }
                        return .{ .ty = exp, .range = null };
                    }
                    if (exp.* == .slice) {
                        return .{ .ty = exp, .range = null };
                    }
                }
                return .{
                    .ty = try self.allocTy(.{ .slice = .{
                        .mutable = false,
                        .elem = elem_ty orelse try self.allocTy(.err),
                    } }),
                    .range = null,
                };
            },
            .block => |*blk| return try self.checkBlock(blk, expected, expected != null),
            .if_expr => |ie| {
                _ = try self.checkExpr(ie.cond, try self.allocTy(.bool));
                const saved_perms = try self.alloc.alloc(BorrowPerm, self.active_views.items.len);
                for (self.active_views.items, 0..) |av, vi| saved_perms[vi] = av.perm;
                const saved_ranges = try self.alloc.alloc(?IntRange, self.scopes.items.len);
                for (self.scopes.items, 0..) |sb, si| saved_ranges[si] = sb.range;
                defer {
                    for (0..saved_ranges.len) |si| {
                        if (si < self.scopes.items.len) self.scopes.items[si].range = saved_ranges[si];
                    }
                }
                self.branch_depth += 1;
                defer self.branch_depth -= 1;

                var then_res: ExprResult = undefined;
                const guard_mark = self.current_sym_guards.items.len;
                defer self.current_sym_guards.shrinkRetainingCapacity(guard_mark);
                {
                    try self.pushScope();
                    defer self.popScope();
                    try self.applyBranchGuard(ie.cond, true);
                    try self.current_sym_guards.append(self.alloc, ie.cond);
                    for (ie.then_block.stmts) |st| try self.checkStmt(&st);
                    then_res = if (ie.then_block.tail) |t|
                        try self.checkExpr(t, expected)
                    else
                        .{ .ty = try self.allocTy(.unit), .range = null };
                }
                self.current_sym_guards.shrinkRetainingCapacity(guard_mark);
                for (0..saved_ranges.len) |si| {
                    if (si < self.scopes.items.len) self.scopes.items[si].range = saved_ranges[si];
                }
                if (ie.else_branch) |eb| {
                    const then_perms = try self.alloc.alloc(BorrowPerm, saved_perms.len);
                    for (0..saved_perms.len) |vi| {
                        then_perms[vi] = self.active_views.items[vi].perm;
                        self.active_views.items[vi].perm = saved_perms[vi];
                    }
                    try self.pushScope();
                    defer self.popScope();
                    try self.applyBranchGuard(ie.cond, false);
                    try self.current_sym_guards.append(self.alloc, try self.invertCondExpr(ie.cond));
                    const else_res = try self.checkExpr(eb, expected);
                    for (0..saved_perms.len) |vi| {
                        if (then_perms[vi] == .active_exclusive) {
                            self.active_views.items[vi].perm = .active_exclusive;
                        }
                    }
                    const joined_range: ?IntRange = if (then_res.range != null and else_res.range != null)
                        then_res.range.?.join(else_res.range.?)
                    else
                        null;
                    if (expected == null and joined_range != null and then_res.ty.isInteger() != null and else_res.ty.isInteger() != null) {
                        if (int_range.inferIntegerType(joined_range.?)) |it| {
                            return .{
                                .ty = try self.allocTy(.{ .int_range = .{ .range = joined_range.?, .synthesized = it } }),
                                .range = joined_range,
                            };
                        }
                    }
                    return .{
                        .ty = then_res.ty,
                        .range = joined_range,
                    };
                }
                return then_res;
            },
            .case_expr => |ce| {
                const sub_types = try self.alloc.alloc(*const Ty, ce.subjects.len);
                for (ce.subjects, 0..) |subj, i| {
                    sub_types[i] = (try self.checkExpr(subj, null)).ty;
                }
                const saved_perms = try self.alloc.alloc(BorrowPerm, self.active_views.items.len);
                const joined_perms = try self.alloc.alloc(BorrowPerm, self.active_views.items.len);
                for (self.active_views.items, 0..) |av, vi| {
                    saved_perms[vi] = av.perm;
                    joined_perms[vi] = av.perm;
                }
                self.branch_depth += 1;
                defer self.branch_depth -= 1;

                var out: ExprResult = .{ .ty = expected orelse try self.allocTy(.unit), .range = null };
                var joined_int_range: ?IntRange = null;
                var all_int_arms = ce.arms.len > 0;
                for (ce.arms, 0..) |arm, ai| {
                    for (0..saved_perms.len) |vi| self.active_views.items[vi].perm = saved_perms[vi];
                    try self.pushScope();
                    defer self.popScope();
                    if (arm.alternatives.len > 0) {
                        for (arm.alternatives[0], 0..) |pat, pi| {
                            const st = if (pi < sub_types.len) sub_types[pi] else try self.allocTy(.err);
                            try self.bindPattern(pat, st, st.rangeOf(), false);
                        }
                    }
                    if (arm.guard) |g| _ = try self.checkExpr(g, try self.allocTy(.bool));
                    const br = try self.checkExpr(arm.body, expected);
                    for (0..saved_perms.len) |vi| {
                        if (self.active_views.items[vi].perm == .active_exclusive) {
                            joined_perms[vi] = .active_exclusive;
                        }
                    }
                    if (br.ty.isInteger() == null) {
                        all_int_arms = false;
                    } else if (br.range orelse br.ty.rangeOf()) |r| {
                        joined_int_range = if (joined_int_range) |jr| jr.join(r) else r;
                    } else {
                        all_int_arms = false;
                    }
                    if (ai == 0) {
                        out = br;
                    } else if (out.range != null and br.range != null) {
                        out.range = out.range.?.join(br.range.?);
                    }
                }
                for (0..joined_perms.len) |vi| self.active_views.items[vi].perm = joined_perms[vi];
                if (expected == null and all_int_arms) {
                    if (joined_int_range) |jr| {
                        if (int_range.inferIntegerType(jr)) |it| {
                            out.ty = try self.allocTy(.{ .int_range = .{ .range = jr, .synthesized = it } });
                            out.range = jr;
                        }
                    }
                }
                return out;
            },
            .lambda => |lam| {
                const exp_fn = if (expected) |e| if (e.* == .fn_ty) e.fn_ty else null else null;
                const outer_scope_end = self.scopes.items.len;
                var free_refs: std.ArrayList(FreeVarRef) = .empty;
                try self.collectFreeRefsBlock(&lam.body, &free_refs);

                var captured_indices: std.ArrayList(usize) = .empty;
                var seen_outer = std.AutoHashMapUnmanaged(usize, void).empty;
                for (free_refs.items) |fref| {
                    var is_param_shadow = false;
                    for (lam.params) |lp| {
                        if (std.mem.eql(u8, lp.name.slice(self.source), fref.name)) {
                            is_param_shadow = true;
                            break;
                        }
                    }
                    if (is_param_shadow) continue;

                    var si = outer_scope_end;
                    while (si > 0) {
                        si -= 1;
                        const ob = &self.scopes.items[si];
                        if (std.mem.eql(u8, ob.name, fref.name)) {
                            if (!seen_outer.contains(si)) {
                                try seen_outer.put(self.alloc, si, {});
                                if (!ob.ty.isCopyable()) {
                                    if (ob.moved) {
                                        self.addError(.use_after_move, fref.span, "use of moved affine resource in closure capture");
                                    } else if (!lam.is_once) {
                                        self.addError(.affine_capture, fref.span, "reusable 'fn' closure cannot capture affine resource; use 'once fn'");
                                    }
                                    try captured_indices.append(self.alloc, si);
                                }
                            }
                            break;
                        }
                    }
                }

                try self.pushScope();
                defer self.popScope();
                const ps = try self.alloc.alloc(*const Ty, lam.params.len);
                for (lam.params, 0..) |p, pi| {
                    const pty = if (p.ty) |t|
                        try self.resolveType(t)
                    else if (exp_fn != null and pi < exp_fn.?.params.len)
                        exp_fn.?.params[pi]
                    else
                        try self.allocTy(.err);
                    ps[pi] = pty;
                    try self.scopes.append(self.alloc, .{
                        .name = p.name.slice(self.source),
                        .ty = pty,
                        .range = pty.rangeOf(),
                        .mutable = p.mutable,
                        .moved = false,
                        .authorized_paths = null,
                        .decl_span = p.span,
                    });
                }
                const ret_exp: ?*const Ty = if (lam.ret) |rt|
                    try self.resolveType(rt)
                else if (exp_fn) |ef|
                    ef.ret
                else
                    null;
                const saved_lam_dec = self.current_fn_decreases;
                self.current_fn_decreases = null;
                defer self.current_fn_decreases = saved_lam_dec;
                const body_res = try self.checkBlock(&lam.body, ret_exp, ret_exp != null);
                if (ret_exp) |re| {
                    if (re.* != .unit or lam.body.tail != null) {
                        try self.checkAssignmentValue(lam.body.span, re, body_res);
                    }
                }
                const ret = ret_exp orelse try self.finalizeInferredType(lam.body.span, body_res);

                if (lam.is_once) {
                    for (captured_indices.items) |idx| {
                        self.scopes.items[idx].moved = true;
                    }
                }

                return .{ .ty = try self.allocTy(.{ .fn_ty = .{ .params = ps, .ret = ret, .is_once = lam.is_once } }), .range = null };
            },
            .view_expr => |vw| {
                const prev_sup = self.suppress_index_access;
                if (vw.target.* == .index) self.suppress_index_access = true;
                const target_res = try self.checkExpr(vw.target, null);
                self.suppress_index_access = prev_sup;

                const mode = vw.mode orelse .shared;
                const init_perm: BorrowPerm = if (mode == .exclusive) .reserved else .shared;

                const target_resolved = if (vw.target.* == .index)
                    self.resolveAccessRoot(vw.target.index.target)
                else
                    self.resolveAccessRoot(vw.target);
                const root_name = target_resolved.root_name orelse "";

                var field_idx: ?usize = null;
                var idx_key: ?AccessIndex = target_resolved.view_index_key;
                if (vw.target.* == .index and idx_key == null) {
                    idx_key = self.extractAccessIndex(vw.target.index.idx);
                }

                const ridx = if (target_res.ty.* == .slice or target_res.ty.* == .collection or
                    (target_res.ty.* == .view and (target_res.ty.view.target.* == .slice or target_res.ty.view.target.* == .collection)))
                    null
                else
                    recordOfType(target_res.ty) orelse blk: {
                        if (vw.target.* == .field) {
                            if (self.expr_types.get(vw.target.field.target)) |ft| {
                                if (recordOfType(ft)) |ri| {
                                    field_idx = self.findRecordField(ri, vw.target.field.name.slice(self.source));
                                    if (vw.target.field.target.* == .index and idx_key == null) {
                                        idx_key = self.extractAccessIndex(vw.target.field.target.index.idx);
                                    }
                                    break :blk ri;
                                }
                            }
                        }
                        break :blk null;
                    };

                // Detect conflict with currently active views using the 4-state permission lattice + AffineIndex disjointness.
                for (self.active_views.items) |av| {
                    if (!av.active) continue;
                    if (std.mem.eql(u8, av.root_name, root_name) and root_name.len > 0) {
                        if (av.index_key != null and idx_key != null) {
                            if (self.accessIndicesDisjoint(av.index_key.?, idx_key.?, true)) continue;
                        }
                        const overlaps = fieldsMayOverlap(av.field_idx, field_idx);
                        if (overlaps and !BorrowPerm.compatible(init_perm, av.perm)) {
                            self.addError(.borrow_conflict, vw.span, "scoped view conflicts with active exclusive or reserved view on the same path");
                        } else if (!overlaps and (mode == .exclusive or av.perm == .reserved or av.perm == .active_exclusive) and ridx != null and av.field_idx != null and field_idx != null) {
                            try self.addConflictEdge(ridx.?, av.field_idx.?, field_idx.?);
                        }
                    }
                }

                try self.pushScope();
                defer self.popScope();

                const vid = self.next_view_id;
                self.next_view_id += 1;

                var early_rel_idx: ?usize = null;
                var is_sentinel = false;
                var bname_opt: ?[]const u8 = null;
                if (vw.binding) |bspan| {
                    const bn = bspan.slice(self.source);
                    bname_opt = bn;
                    if (self.blockMentionsIdent(&vw.body, bn)) {
                        early_rel_idx = self.lastUseStmtInBlock(&vw.body, bn);
                    } else {
                        is_sentinel = true;
                    }
                }

                const in_trace = (self.branch_depth == 0 and ridx != null and idx_key == null and self.current_perm_trace != null);
                if (in_trace) {
                    try self.current_perm_trace.?.append(self.alloc, .{ .reserve = .{
                        .view_id = vid,
                        .root_name = root_name,
                        .record_idx = ridx.?,
                        .field_idx = field_idx,
                        .perm = init_perm,
                    } });
                }

                try self.active_views.append(self.alloc, .{
                    .id = vid,
                    .binding_name = bname_opt,
                    .root_name = root_name,
                    .record_idx = ridx,
                    .field_idx = field_idx,
                    .index_key = idx_key,
                    .perm = init_perm,
                    .active = true,
                    .is_sentinel = is_sentinel,
                    .in_trace = in_trace,
                });

                if (bname_opt) |bn| {
                    const bspan = vw.binding.?;
                    var target_is_caller_rooted = false;
                    var caller_param_idx: ?usize = null;
                    if (self.extractRootIdent(vw.target)) |rn| {
                        if (self.lookupVar(rn)) |src_vb| {
                            if (src_vb.view_is_caller_rooted or (src_vb.is_param and (src_vb.ty.* == .path_borrow or src_vb.ty.* == .view or src_vb.ty.* == .slice or src_vb.ty.* == .collection))) {
                                target_is_caller_rooted = true;
                                caller_param_idx = src_vb.param_index;
                            }
                        }
                    }
                    const view_ty = try self.allocTy(.{ .view = .{
                        .mode = mode,
                        .target = target_res.ty,
                        .target_record = ridx,
                    } });
                    try self.scopes.append(self.alloc, .{
                        .name = bn,
                        .ty = view_ty,
                        .range = null,
                        .mutable = mode == .exclusive,
                        .moved = false,
                        .authorized_paths = null,
                        .decl_span = bspan,
                        .param_index = caller_param_idx,
                        .view_id = vid,
                        .view_root = if (root_name.len > 0) root_name else null,
                        .view_record_idx = ridx,
                        .view_field_idx = field_idx,
                        .view_index_key = idx_key,
                        .view_is_caller_rooted = target_is_caller_rooted,
                    });
                }

                return try self.checkBlockWithViewRelease(&vw.body, expected, false, vid, early_rel_idx);
            },
            .fork_expr => |fk| {
                // Collect footprints independently for every concurrent branch.
                const branch_lists = try self.alloc.alloc(std.ArrayList(AccessRecord), fk.branches.len);
                const prev_acc = self.current_accesses;
                const prev_fork_start = self.active_fork_start;
                defer {
                    self.current_accesses = prev_acc;
                    self.active_fork_start = prev_fork_start;
                }

                for (fk.branches, 0..) |*br, bi| {
                    branch_lists[bi] = .empty;
                    self.current_accesses = &branch_lists[bi];
                    self.active_fork_start = fk.span.start;
                    _ = try self.checkBlock(br, null, false);
                }
                self.active_fork_start = prev_fork_start;

                // Pairwise disjointness check (ScopedForkJoin.lean + AffineIndex.lean).
                var i: usize = 0;
                while (i < branch_lists.len) : (i += 1) {
                    var j: usize = i + 1;
                    while (j < branch_lists.len) : (j += 1) {
                        for (branch_lists[i].items) |a| {
                            for (branch_lists[j].items) |b| {
                                if (!std.mem.eql(u8, a.root_name, b.root_name)) continue;
                                if (!a.is_write and !b.is_write) continue; // Read-read safe!
                                if (a.index_key != null and b.index_key != null) {
                                    if (self.accessIndicesDisjoint(a.index_key.?, b.index_key.?, true)) continue;
                                }
                                const same_field = fieldsMayOverlap(a.field_idx, b.field_idx);
                                if (same_field) {
                                    self.addError(.fork_data_race, b.span, "fork/join data race: concurrent branches share conflicting read/write or write/write access");
                                } else if (a.record_idx != null and a.field_idx != null and b.field_idx != null) {
                                    // Distinct sibling fields written concurrently forbid same-byte packing!
                                    try self.addConflictEdge(a.record_idx.?, a.field_idx.?, b.field_idx.?);
                                }
                            }
                        }
                    }
                }

                // Propagate combined accesses to enclosing function effect list.
                if (prev_acc) |outer| {
                    for (branch_lists) |bl| {
                        for (bl.items) |acc| try outer.append(self.alloc, acc);
                    }
                }

                return .{ .ty = try self.allocTy(.unit), .range = null };
            },
            .todo_expr => |td| {
                if (td.message) |m| _ = try self.checkExpr(m, try self.allocTy(.string));
                return .{ .ty = expected orelse try self.allocTy(.err), .range = null };
            },
            .panic_expr => |pn| {
                if (pn.message) |m| _ = try self.checkExpr(m, try self.allocTy(.string));
                return .{ .ty = expected orelse try self.allocTy(.err), .range = null };
            },
            .err => return .{ .ty = try self.allocTy(.err), .range = null },
        }
    }

    fn lookupConstructorVariant(self: *const Analyzer, path: []const ast.Span, expected_ty: *const Ty) ?VariantInfo {
        if (path.len == 0) return null;
        const vname = path[path.len - 1].slice(self.source);
        if (path.len >= 2) {
            const adt_name = path[path.len - 2].slice(self.source);
            if (self.findADTIndex(adt_name)) |aidx| {
                for (self.adt_defs.items[aidx].variants) |v| {
                    if (std.mem.eql(u8, v.name, vname)) return v;
                }
            }
        }
        if (expected_ty.* == .adt) {
            for (self.adt_defs.items[expected_ty.adt].variants) |v| {
                if (std.mem.eql(u8, v.name, vname)) return v;
            }
        }
        for (self.adt_defs.items) |adt_def| {
            for (adt_def.variants) |v| {
                if (std.mem.eql(u8, v.name, vname)) return v;
            }
        }
        return null;
    }

    fn builtinPrintKind(self: *const Analyzer, callee: *const ast.Expr) bool {
        const name: []const u8 = switch (callee.*) {
            .ident => |sp| sp.slice(self.source),
            .field => |fld| blk: {
                if (fld.target.* == .ident and std.mem.eql(u8, fld.target.ident.slice(self.source), "io")) {
                    break :blk fld.name.slice(self.source);
                }
                return false;
            },
            else => return false,
        };
        return std.mem.eql(u8, name, "println") or
            std.mem.eql(u8, name, "print") or
            std.mem.eql(u8, name, "eprintln") or
            std.mem.eql(u8, name, "eprint");
    }

    fn lookupADTVariantType(self: *Analyzer, variant_name: []const u8) ?*const Ty {
        for (self.adt_defs.items, 0..) |adt_def, aidx| {
            for (adt_def.variants) |v| {
                if (std.mem.eql(u8, v.name, variant_name)) {
                    return self.allocTy(.{ .adt = aidx }) catch null;
                }
            }
        }
        return null;
    }

    const FreeVarRef = struct {
        name: []const u8,
        span: ast.Span,
    };

    fn isInLocals(locals: []const []const u8, name: []const u8) bool {
        for (locals) |l| if (std.mem.eql(u8, l, name)) return true;
        return false;
    }

    fn collectPatNames(self: *const Analyzer, pat: *const ast.Pattern, locals: *std.ArrayList([]const u8)) std.mem.Allocator.Error!void {
        switch (pat.*) {
            .ident => |id| try locals.append(self.alloc, id.name.slice(self.source)),
            .tuple => |tp| for (tp.elems) |el| try self.collectPatNames(el, locals),
            .constructor => |c| for (c.args) |a| try self.collectPatNames(a.pattern, locals),
            .alias => |al| {
                try self.collectPatNames(al.inner, locals);
                try locals.append(self.alloc, al.name.slice(self.source));
            },
            .list => |lp| {
                for (lp.elems) |el| try self.collectPatNames(el, locals);
                if (lp.rest) |rsp| try locals.append(self.alloc, rsp.slice(self.source));
            },
            .or_pat => |op| if (op.alternatives.len > 0) try self.collectPatNames(op.alternatives[0], locals),
            else => {},
        }
    }

    fn collectFreeRefsBlock(self: *const Analyzer, blk: *const ast.Block, out: *std.ArrayList(FreeVarRef)) std.mem.Allocator.Error!void {
        var locals: std.ArrayList([]const u8) = .empty;
        try self.collectFreeRefsBlockScoped(blk, &locals, out);
    }

    fn collectFreeRefsBlockScoped(
        self: *const Analyzer,
        blk: *const ast.Block,
        locals: *std.ArrayList([]const u8),
        out: *std.ArrayList(FreeVarRef),
    ) std.mem.Allocator.Error!void {
        const lmark = locals.items.len;
        defer locals.shrinkRetainingCapacity(lmark);
        for (blk.stmts) |*st| {
            switch (st.*) {
                .let_stmt => |ls| {
                    try self.collectFreeRefsExprScoped(ls.value, locals, out);
                    try self.collectPatNames(ls.pattern, locals);
                },
                .use_stmt => |us| {
                    try self.collectFreeRefsExprScoped(us.expr, locals, out);
                    for (us.patterns) |p| try self.collectPatNames(p, locals);
                },
                .assign_stmt => |asg| {
                    try self.collectFreeRefsExprScoped(asg.target, locals, out);
                    try self.collectFreeRefsExprScoped(asg.value, locals, out);
                },
                .return_stmt => |rs| if (rs.value) |v| try self.collectFreeRefsExprScoped(v, locals, out),
                .while_stmt => |ws| {
                    try self.collectFreeRefsExprScoped(ws.cond, locals, out);
                    try self.collectFreeRefsBlockScoped(&ws.body, locals, out);
                },
                .for_stmt => |fs| {
                    try self.collectFreeRefsExprScoped(fs.iter, locals, out);
                    const fmark = locals.items.len;
                    defer locals.shrinkRetainingCapacity(fmark);
                    try self.collectPatNames(fs.pattern, locals);
                    try self.collectFreeRefsBlockScoped(&fs.body, locals, out);
                },
                .expr_stmt => |es| try self.collectFreeRefsExprScoped(es.expr, locals, out),
            }
        }
        if (blk.tail) |t| try self.collectFreeRefsExprScoped(t, locals, out);
    }

    fn collectFreeRefsExprScoped(
        self: *const Analyzer,
        expr: *const ast.Expr,
        locals: *std.ArrayList([]const u8),
        out: *std.ArrayList(FreeVarRef),
    ) std.mem.Allocator.Error!void {
        switch (expr.*) {
            .ident => |sp| {
                const name = sp.slice(self.source);
                if (!isInLocals(locals.items, name)) {
                    try out.append(self.alloc, .{ .name = name, .span = sp });
                }
            },
            .unary => |u| try self.collectFreeRefsExprScoped(u.operand, locals, out),
            .binary => |b| {
                try self.collectFreeRefsExprScoped(b.left, locals, out);
                try self.collectFreeRefsExprScoped(b.right, locals, out);
            },
            .cast => |c| try self.collectFreeRefsExprScoped(c.expr, locals, out),
            .call => |c| {
                try self.collectFreeRefsExprScoped(c.callee, locals, out);
                for (c.args) |a| try self.collectFreeRefsExprScoped(a.value, locals, out);
            },
            .field => |fld| try self.collectFreeRefsExprScoped(fld.target, locals, out),
            .index => |ix| {
                try self.collectFreeRefsExprScoped(ix.target, locals, out);
                try self.collectFreeRefsExprScoped(ix.idx, locals, out);
            },
            .try_op => |t| try self.collectFreeRefsExprScoped(t.operand, locals, out),
            .record_lit => |rl| {
                for (rl.fields) |rf| {
                    if (rf.value) |v| {
                        try self.collectFreeRefsExprScoped(v, locals, out);
                    } else {
                        const name = rf.name.slice(self.source);
                        if (!isInLocals(locals.items, name)) {
                            try out.append(self.alloc, .{ .name = name, .span = rf.name });
                        }
                    }
                }
            },
            .tuple => |tp| for (tp.elems) |el| try self.collectFreeRefsExprScoped(el, locals, out),
            .list => |ls| for (ls.elems) |el| try self.collectFreeRefsExprScoped(el, locals, out),
            .block => |*blk| try self.collectFreeRefsBlockScoped(blk, locals, out),
            .if_expr => |ie| {
                try self.collectFreeRefsExprScoped(ie.cond, locals, out);
                try self.collectFreeRefsBlockScoped(&ie.then_block, locals, out);
                if (ie.else_branch) |eb| try self.collectFreeRefsExprScoped(eb, locals, out);
            },
            .case_expr => |ce| {
                for (ce.subjects) |s| try self.collectFreeRefsExprScoped(s, locals, out);
                for (ce.arms) |arm| {
                    const amark = locals.items.len;
                    defer locals.shrinkRetainingCapacity(amark);
                    if (arm.alternatives.len > 0) {
                        for (arm.alternatives[0]) |p| try self.collectPatNames(p, locals);
                    }
                    if (arm.guard) |g| try self.collectFreeRefsExprScoped(g, locals, out);
                    try self.collectFreeRefsExprScoped(arm.body, locals, out);
                }
            },
            .lambda => |lam| {
                const lmark = locals.items.len;
                defer locals.shrinkRetainingCapacity(lmark);
                for (lam.params) |p| try locals.append(self.alloc, p.name.slice(self.source));
                try self.collectFreeRefsBlockScoped(&lam.body, locals, out);
            },
            .view_expr => |vw| {
                try self.collectFreeRefsExprScoped(vw.target, locals, out);
                const vmark = locals.items.len;
                defer locals.shrinkRetainingCapacity(vmark);
                if (vw.binding) |bs| try locals.append(self.alloc, bs.slice(self.source));
                try self.collectFreeRefsBlockScoped(&vw.body, locals, out);
            },
            .fork_expr => |fk| for (fk.branches) |*br| try self.collectFreeRefsBlockScoped(br, locals, out),
            .todo_expr => |td| if (td.message) |m| try self.collectFreeRefsExprScoped(m, locals, out),
            .panic_expr => |pn| if (pn.message) |m| try self.collectFreeRefsExprScoped(m, locals, out),
            else => {},
        }
    }

    fn checkPipeline(
        self: *Analyzer,
        full_expr: *const ast.Expr,
        left: *const ast.Expr,
        right: *const ast.Expr,
        expected: ?*const Ty,
    ) std.mem.Allocator.Error!ExprResult {
        _ = full_expr;
        const left_res = try self.checkExpr(left, null);
        if (right.* == .call) {
            const call_res = try self.checkCall(right, right.call.span, right.call.callee, right.call.args, left_res, left, expected);
            try self.expr_types.put(self.alloc, right, call_res.ty);
            return call_res;
        }
        return try self.checkExpr(right, expected);
    }

    fn checkMapperFnArg(
        self: *Analyzer,
        span: ast.Span,
        arg_expr: *const ast.Expr,
        in_ty: *const Ty,
        expected_out: ?*const Ty,
    ) std.mem.Allocator.Error!*const Ty {
        if (arg_expr.* == .lambda) {
            const lam = arg_expr.lambda;
            const res = try self.checkExprInnerLambdaWithHint(&lam, in_ty, expected_out);
            try self.expr_types.put(self.alloc, arg_expr, res.ty);
            return res.ty.fn_ty.ret;
        }
        const res = try self.checkExpr(arg_expr, null);
        if (res.ty.* == .fn_ty) {
            if (arg_expr.* == .ident and res.ty.fn_ty.is_once) {
                if (self.lookupVar(arg_expr.ident.slice(self.source))) |vb| {
                    vb.moved = true;
                }
            }
            if (res.ty.fn_ty.params.len >= 1) {
                try self.checkAssignmentValue(span, res.ty.fn_ty.params[0], .{ .ty = in_ty, .range = in_ty.rangeOf() });
            }
            return res.ty.fn_ty.ret;
        }
        if (res.ty.* != .err) {
            self.addError(.type_mismatch, span, "combinator expected a function or lambda argument");
        }
        return try self.allocTy(.err);
    }

    fn checkExprInnerLambdaWithHint(
        self: *Analyzer,
        lam: anytype,
        param0_ty: *const Ty,
        ret_hint: ?*const Ty,
    ) std.mem.Allocator.Error!ExprResult {
        const outer_scope_end = self.scopes.items.len;
        var free_refs: std.ArrayList(FreeVarRef) = .empty;
        try self.collectFreeRefsBlock(&lam.body, &free_refs);
        var captured_indices: std.ArrayList(usize) = .empty;
        var seen_outer = std.AutoHashMapUnmanaged(usize, void).empty;
        for (free_refs.items) |fref| {
            var is_param_shadow = false;
            for (lam.params) |lp| {
                if (std.mem.eql(u8, lp.name.slice(self.source), fref.name)) {
                    is_param_shadow = true;
                    break;
                }
            }
            if (is_param_shadow) continue;
            var si = outer_scope_end;
            while (si > 0) {
                si -= 1;
                const ob = &self.scopes.items[si];
                if (std.mem.eql(u8, ob.name, fref.name)) {
                    if (!seen_outer.contains(si)) {
                        try seen_outer.put(self.alloc, si, {});
                        if (!ob.ty.isCopyable()) {
                            if (ob.moved) {
                                self.addError(.use_after_move, fref.span, "use of moved affine resource in closure capture");
                            } else if (!lam.is_once) {
                                self.addError(.affine_capture, fref.span, "reusable 'fn' closure cannot capture affine resource; use 'once fn'");
                            }
                            try captured_indices.append(self.alloc, si);
                        }
                    }
                    break;
                }
            }
        }
        try self.pushScope();
        defer self.popScope();
        const ps = try self.alloc.alloc(*const Ty, lam.params.len);
        for (lam.params, 0..) |p, pi| {
            const pty = if (p.ty) |t|
                try self.resolveType(t)
            else if (pi == 0)
                param0_ty
            else
                try self.allocTy(.err);
            ps[pi] = pty;
            try self.scopes.append(self.alloc, .{
                .name = p.name.slice(self.source),
                .ty = pty,
                .range = pty.rangeOf(),
                .mutable = p.mutable,
                .moved = false,
                .authorized_paths = null,
                .decl_span = p.span,
            });
        }
        const ret_exp: ?*const Ty = if (lam.ret) |rt| try self.resolveType(rt) else ret_hint;
        const saved_lam_dec = self.current_fn_decreases;
        self.current_fn_decreases = null;
        defer self.current_fn_decreases = saved_lam_dec;
        const body_res = try self.checkBlock(&lam.body, ret_exp, ret_exp != null);
        if (ret_exp) |re| {
            if (re.* != .unit or lam.body.tail != null) {
                try self.checkAssignmentValue(lam.body.span, re, body_res);
            }
        }
        const ret = ret_exp orelse try self.finalizeInferredType(lam.body.span, body_res);
        if (lam.is_once) {
            for (captured_indices.items) |idx| self.scopes.items[idx].moved = true;
        }
        return .{ .ty = try self.allocTy(.{ .fn_ty = .{ .params = ps, .ret = ret, .is_once = lam.is_once } }), .range = null };
    }

    fn collectionElemTy(ty: *const Ty) ?*const Ty {
        return switch (ty.*) {
            .collection => |c| c.elem_ty,
            .slice => |s| s.elem,
            .view => |v| switch (v.target.*) {
                .collection => |c| c.elem_ty,
                .slice => |s| s.elem,
                else => null,
            },
            .path_borrow => |pb| switch (pb.base.*) {
                .collection => |c| c.elem_ty,
                .slice => |s| s.elem,
                else => null,
            },
            else => null,
        };
    }

    fn checkCall(
        self: *Analyzer,
        call_expr: *const ast.Expr,
        span: ast.Span,
        callee: *const ast.Expr,
        args: []const ast.CallArg,
        piped_recv: ?ExprResult,
        piped_recv_expr: ?*const ast.Expr,
        expected: ?*const Ty,
    ) std.mem.Allocator.Error!ExprResult {
        // Built-in I/O (`println`, `print`, `eprintln`, `eprint` and `io.*` forms).
        if (self.builtinPrintKind(callee)) {
            for (args) |arg| {
                _ = try self.checkExpr(arg.value, null);
            }
            return .{ .ty = try self.allocTy(.unit), .range = null };
        }

        // Special-case collection/option/result higher-order combinators (`map_in_place`, `fold`, `map`, `and_then`, `unwrap_or`, `ok_or`).
        if (callee.* == .ident) {
            const cname = callee.ident.slice(self.source);
            if (std.mem.eql(u8, cname, "map_in_place") and piped_recv != null and args.len == 1 and args[0].value.* == .lambda) {
                const lam = args[0].value.lambda;
                if (recordOfType(piped_recv.?.ty)) |ridx| {
                    var auth: ?[]const usize = null;
                    if (piped_recv.?.ty.* == .path_borrow) {
                        auth = try self.extractAuthorizedPaths(span, piped_recv.?.ty);
                    }
                    try self.pushScope();
                    defer self.popScope();
                    if (lam.params.len > 0) {
                        const elem_ty = try self.allocTy(.{ .record = ridx });
                        try self.scopes.append(self.alloc, .{
                            .name = lam.params[0].name.slice(self.source),
                            .ty = elem_ty,
                            .range = null,
                            .mutable = true,
                            .moved = false,
                            .authorized_paths = auth,
                            .decl_span = lam.params[0].span,
                        });
                    }
                    const acc_start = if (self.current_accesses) |al| al.items.len else 0;
                    _ = try self.checkBlock(&lam.body, null, false);
                    self.markHotFieldsSince(ridx, acc_start);
                    if (lam.params.len == 1 and self.isSimdVectorizableLambda(ridx, lam.params[0].name.slice(self.source), &lam.body)) {
                        self.record_defs.items[ridx].simd_loop_seen = true;
                    }
                    return .{ .ty = piped_recv.?.ty, .range = null };
                }
            }
            if (std.mem.eql(u8, cname, "fold") and piped_recv != null and args.len == 2) {
                if (collectionElemTy(piped_recv.?.ty)) |elem_ty| {
                    const init_res = try self.checkExpr(args[0].value, expected);
                    const acc_ty = expected orelse try self.finalizeInferredType(args[0].span, init_res);
                    if (args[1].value.* == .lambda) {
                        const lam = args[1].value.lambda;
                        try self.pushScope();
                        defer self.popScope();
                        if (lam.params.len >= 1) {
                            try self.scopes.append(self.alloc, .{
                                .name = lam.params[0].name.slice(self.source),
                                .ty = acc_ty,
                                .range = acc_ty.rangeOf(),
                                .mutable = false,
                                .moved = false,
                                .authorized_paths = null,
                                .decl_span = lam.params[0].span,
                            });
                        }
                        if (lam.params.len >= 2) {
                            try self.scopes.append(self.alloc, .{
                                .name = lam.params[1].name.slice(self.source),
                                .ty = elem_ty,
                                .range = elem_ty.rangeOf(),
                                .mutable = false,
                                .moved = false,
                                .authorized_paths = null,
                                .decl_span = lam.params[1].span,
                            });
                        }
                        const acc_start = if (self.current_accesses) |al| al.items.len else 0;
                        const body_res = try self.checkBlock(&lam.body, acc_ty, true);
                        try self.checkAssignmentValue(args[1].span, acc_ty, body_res);
                        if (recordOfType(elem_ty)) |ridx| self.markHotFieldsSince(ridx, acc_start);
                        try self.expr_types.put(self.alloc, args[1].value, try self.allocTy(.{ .fn_ty = .{
                            .params = try self.alloc.dupe(*const Ty, &.{ acc_ty, elem_ty }),
                            .ret = acc_ty,
                            .is_once = lam.is_once,
                        } }));
                    } else {
                        const fn_res = try self.checkExpr(args[1].value, null);
                        if (fn_res.ty.* == .fn_ty and fn_res.ty.fn_ty.params.len == 2) {
                            try self.checkAssignmentValue(args[1].span, acc_ty, .{ .ty = fn_res.ty.fn_ty.ret, .range = null });
                        }
                    }
                    return .{ .ty = acc_ty, .range = acc_ty.rangeOf() };
                }
            }
            if ((std.mem.eql(u8, cname, "map") or std.mem.eql(u8, cname, "and_then") or
                std.mem.eql(u8, cname, "unwrap_or") or std.mem.eql(u8, cname, "ok_or")) and
                ((piped_recv != null and args.len == 1) or (piped_recv == null and args.len == 2)))
            {
                const recv_res = piped_recv orelse try self.checkExpr(args[0].value, null);
                const comb_arg = if (piped_recv != null) args[0] else args[1];
                if (recv_res.ty.* == .option) {
                    const inner_ty = recv_res.ty.option;
                    if (std.mem.eql(u8, cname, "map")) {
                        const exp_out = if (expected != null and expected.?.* == .option) expected.?.option else null;
                        const out_ty = try self.checkMapperFnArg(comb_arg.span, comb_arg.value, inner_ty, exp_out);
                        return .{ .ty = try self.allocTy(.{ .option = out_ty }), .range = null };
                    }
                    if (std.mem.eql(u8, cname, "and_then")) {
                        const out_ty = try self.checkMapperFnArg(comb_arg.span, comb_arg.value, inner_ty, expected);
                        if (out_ty.* != .option and out_ty.* != .err) {
                            self.addError(.type_mismatch, comb_arg.span, "Option and_then callback must return Option(...)");
                            return .{ .ty = try self.allocTy(.{ .option = try self.allocTy(.err) }), .range = null };
                        }
                        return .{ .ty = out_ty, .range = null };
                    }
                    if (std.mem.eql(u8, cname, "unwrap_or")) {
                        const def_res = try self.checkExpr(comb_arg.value, inner_ty);
                        try self.checkAssignmentValue(comb_arg.span, inner_ty, def_res);
                        return .{ .ty = inner_ty, .range = inner_ty.rangeOf() };
                    }
                    if (std.mem.eql(u8, cname, "ok_or")) {
                        const exp_err = if (expected != null and expected.?.* == .result) expected.?.result.err else null;
                        const err_res = try self.checkExpr(comb_arg.value, exp_err);
                        const err_ty = exp_err orelse try self.finalizeInferredType(comb_arg.span, err_res);
                        if (exp_err) |ee| try self.checkAssignmentValue(comb_arg.span, ee, err_res);
                        return .{ .ty = try self.allocTy(.{ .result = .{ .ok = inner_ty, .err = err_ty } }), .range = null };
                    }
                }
                if (recv_res.ty.* == .result) {
                    const res_ty = recv_res.ty.result;
                    if (std.mem.eql(u8, cname, "map")) {
                        const exp_ok = if (expected != null and expected.?.* == .result) expected.?.result.ok else null;
                        const out_ok = try self.checkMapperFnArg(comb_arg.span, comb_arg.value, res_ty.ok, exp_ok);
                        return .{ .ty = try self.allocTy(.{ .result = .{ .ok = out_ok, .err = res_ty.err } }), .range = null };
                    }
                    if (std.mem.eql(u8, cname, "and_then")) {
                        const out_ty = try self.checkMapperFnArg(comb_arg.span, comb_arg.value, res_ty.ok, expected);
                        if (out_ty.* != .result and out_ty.* != .err) {
                            self.addError(.type_mismatch, comb_arg.span, "Result and_then callback must return Result(...)");
                            return .{ .ty = try self.allocTy(.{ .result = .{ .ok = try self.allocTy(.err), .err = res_ty.err } }), .range = null };
                        }
                        if (out_ty.* == .result) {
                            const out_r = out_ty.result;
                            if (res_ty.err.* != .err and out_r.err.* != .err) {
                                try self.checkAssignmentValue(comb_arg.span, res_ty.err, .{ .ty = out_r.err, .range = null });
                            }
                            const final_err = if (res_ty.err.* != .err) res_ty.err else out_r.err;
                            return .{ .ty = try self.allocTy(.{ .result = .{ .ok = out_r.ok, .err = final_err } }), .range = null };
                        }
                        return .{ .ty = out_ty, .range = null };
                    }
                    if (std.mem.eql(u8, cname, "unwrap_or")) {
                        const def_res = try self.checkExpr(comb_arg.value, res_ty.ok);
                        try self.checkAssignmentValue(comb_arg.span, res_ty.ok, def_res);
                        return .{ .ty = res_ty.ok, .range = res_ty.ok.rangeOf() };
                    }
                }
            }
            if ((std.mem.eql(u8, cname, "min") or std.mem.eql(u8, cname, "max")) and piped_recv == null and args.len == 2) {
                const ar0 = try self.checkExpr(args[0].value, expected);
                const ar1 = try self.checkExpr(args[1].value, ar0.ty);
                const r0 = ar0.range orelse ar0.ty.rangeOf();
                const r1 = ar1.range orelse ar1.ty.rangeOf();
                const res_ty = if (ar0.ty.* != .err and ar0.ty.* != .int_range) ar0.ty else ar1.ty;
                const rng: ?IntRange = if (r0 != null and r1 != null and r0.? == .bounded and r1.? == .bounded) blk: {
                    const b0 = r0.?.bounded;
                    const b1 = r1.?.bounded;
                    break :blk if (std.mem.eql(u8, cname, "min"))
                        .{ .bounded = .{ .lo = @min(b0.lo, b1.lo), .hi = @min(b0.hi, b1.hi) } }
                    else
                        .{ .bounded = .{ .lo = @max(b0.lo, b1.lo), .hi = @max(b0.hi, b1.hi) } };
                } else r0 orelse r1;
                return .{ .ty = res_ty, .range = rng };
            }
            if (self.findFnIndex(cname)) |fidx| {
                const fsig = self.fn_sigs.items[fidx];
                const recv_offset: usize = if (piped_recv != null) 1 else 0;
                var subst: std.StringHashMapUnmanaged(*const Ty) = .empty;
                if (piped_recv) |pr| {
                    if (fsig.params.len > 0) {
                        if (fsig.type_params.len > 0) {
                            if (!try self.unifyType(fsig.params[0], pr.ty, &subst)) {
                                self.addError(.type_mismatch, span, "generic receiver type mismatch");
                            }
                        } else {
                            try self.checkAssignmentValue(span, fsig.params[0], pr);
                        }
                    }
                }
                for (args, 0..) |arg, ai| {
                    const param_idx = ai + recv_offset;
                    const expected_p = if (param_idx < fsig.params.len) fsig.params[param_idx] else null;
                    if (fsig.type_params.len > 0 and expected_p != null) {
                        const ep_sub = try self.substituteType(expected_p.?, &subst);
                        const has_free = containsUnresolvedTypeVar(ep_sub, &subst);
                        const ar = try self.checkExpr(arg.value, if (has_free) null else ep_sub);
                        const final_ar_ty = if (has_free)
                            try self.finalizeInferredType(arg.value.getSpan(), ar)
                        else
                            ar.ty;
                        if (!ep_sub.isCopyable() and arg.value.* == .ident) {
                            const vname = arg.value.ident.slice(self.source);
                            if (self.lookupVar(vname)) |vb| {
                                if (ep_sub.* != .view and ep_sub.* != .slice and ep_sub.* != .path_borrow) {
                                    vb.moved = true;
                                }
                            }
                        }
                        if (!try self.unifyType(expected_p.?, final_ar_ty, &subst)) {
                            self.addError(.type_mismatch, arg.span, "argument does not match generic function type parameter");
                        }
                    } else {
                        const ar = try self.checkExpr(arg.value, expected_p);
                        if (expected_p) |ep| {
                            if (!ep.isCopyable() and arg.value.* == .ident) {
                                const vname = arg.value.ident.slice(self.source);
                                if (self.lookupVar(vname)) |vb| {
                                    if (ep.* != .view and ep.* != .slice and ep.* != .path_borrow) {
                                        vb.moved = true;
                                    }
                                }
                            }
                            try self.checkAssignmentValue(arg.span, ep, ar);
                        }
                    }
                }
                if (fsig.type_params.len > 0) {
                    const concrete = try self.alloc.alloc(*const Ty, fsig.type_params.len);
                    for (fsig.type_params, 0..) |tp, ti| {
                        concrete[ti] = subst.get(tp) orelse try self.allocTy(.{ .type_var = tp });
                    }
                    try self.call_type_args.put(self.alloc, call_expr, concrete);
                }
                // Propagate transitive callee reads/writes onto actual arguments (InterprocBorrow.lean).
                for (fsig.param_writes.items) |pw| {
                    const actual_expr: ?*const ast.Expr = if (piped_recv != null and pw.param_idx == 0)
                        piped_recv_expr
                    else if (pw.param_idx >= recv_offset and (pw.param_idx - recv_offset) < args.len)
                        args[pw.param_idx - recv_offset].value
                    else
                        null;
                    if (actual_expr) |ae| {
                        try self.propagateArgEffect(ae, pw.record_idx, pw.field_idx, true, span);
                    }
                }
                for (fsig.param_reads.items) |pr| {
                    const actual_expr: ?*const ast.Expr = if (piped_recv != null and pr.param_idx == 0)
                        piped_recv_expr
                    else if (pr.param_idx >= recv_offset and (pr.param_idx - recv_offset) < args.len)
                        args[pr.param_idx - recv_offset].value
                    else
                        null;
                    if (actual_expr) |ae| {
                        try self.propagateArgEffect(ae, pr.record_idx, pr.field_idx, false, span);
                    }
                }
                // Also track non-record slice/view arguments inside fork/view checks when callee takes mutable/shared view or slice.
                for (fsig.params, 0..) |ep, pidx| {
                    const ae: ?*const ast.Expr = if (piped_recv != null and pidx == 0)
                        piped_recv_expr
                    else if (pidx >= recv_offset and (pidx - recv_offset) < args.len)
                        args[pidx - recv_offset].value
                    else
                        null;
                    if (ae) |actual| {
                        if (recordOfType(ep) == null) {
                            const is_slice_mut = ep.* == .slice and ep.slice.mutable;
                            const is_view_mut = ep.* == .view and ep.view.mode == .exclusive;
                            const is_slice_ro = ep.* == .slice and !ep.slice.mutable;
                            const is_view_ro = ep.* == .view and ep.view.mode == .shared;
                            if (is_slice_mut or is_view_mut or is_slice_ro or is_view_ro) {
                                const resolved = self.resolveAccessRoot(actual);
                                if (resolved.root_name) |rn| {
                                    const idx_key: ?AccessIndex = resolved.view_index_key orelse if (actual.* == .index)
                                        self.extractAccessIndex(actual.index.idx)
                                    else
                                        null;
                                    try self.recordAccess(rn, null, null, is_slice_mut or is_view_mut, span, idx_key, resolved.through_view_id);
                                }
                            }
                        }
                    }
                }
                if (piped_recv == null and self.current_fn_name != null and self.current_fn_decreases != null and std.mem.eql(u8, cname, self.current_fn_name.?)) {
                    const arg_exprs = try self.alloc.alloc(*const ast.Expr, args.len);
                    for (args, 0..) |a, ai| arg_exprs[ai] = a.value;
                    try self.verifyRecursiveDecreasesCall(span, arg_exprs);
                }
                const final_ret = if (fsig.type_params.len > 0) try self.substituteType(fsig.ret, &subst) else fsig.ret;
                return .{ .ty = final_ret, .range = final_ret.rangeOf() };
            }
        }

        if (callee.* == .upper_ident) {
            const cname = callee.upper_ident.slice(self.source);
            if (std.mem.eql(u8, cname, "Some") and args.len == 1) {
                const exp_inner: ?*const Ty = if (expected != null and expected.?.* == .option) expected.?.option else null;
                const inner = try self.checkExpr(args[0].value, exp_inner);
                const inner_ty = exp_inner orelse try self.finalizeInferredType(args[0].span, inner);
                if (exp_inner) |ei| try self.checkAssignmentValue(args[0].span, ei, inner);
                return .{ .ty = try self.allocTy(.{ .option = inner_ty }), .range = null };
            }
            if (std.mem.eql(u8, cname, "Ok") and args.len == 1) {
                const exp_ok: ?*const Ty = if (expected != null and expected.?.* == .result) expected.?.result.ok else null;
                const exp_err: ?*const Ty = if (expected != null and expected.?.* == .result) expected.?.result.err else null;
                const inner = try self.checkExpr(args[0].value, exp_ok);
                const ok_ty = exp_ok orelse try self.finalizeInferredType(args[0].span, inner);
                if (exp_ok) |eo| try self.checkAssignmentValue(args[0].span, eo, inner);
                return .{ .ty = try self.allocTy(.{ .result = .{ .ok = ok_ty, .err = exp_err orelse try self.allocTy(.err) } }), .range = null };
            }
            if (std.mem.eql(u8, cname, "Err") and args.len == 1) {
                const exp_ok: ?*const Ty = if (expected != null and expected.?.* == .result) expected.?.result.ok else null;
                const exp_err: ?*const Ty = if (expected != null and expected.?.* == .result) expected.?.result.err else null;
                const inner = try self.checkExpr(args[0].value, exp_err);
                const err_ty = exp_err orelse try self.finalizeInferredType(args[0].span, inner);
                if (exp_err) |ee| try self.checkAssignmentValue(args[0].span, ee, inner);
                return .{ .ty = try self.allocTy(.{ .result = .{ .ok = exp_ok orelse try self.allocTy(.err), .err = err_ty } }), .range = null };
            }
            for (self.adt_defs.items, 0..) |adt_def, aidx| {
                for (adt_def.variants) |v| {
                    if (std.mem.eql(u8, v.name, cname)) {
                        for (args, 0..) |arg, ai| {
                            const exp_ft: ?*const Ty = if (ai < v.field_types.len) v.field_types[ai] else null;
                            const ar = try self.checkExpr(arg.value, exp_ft);
                            if (exp_ft) |ft| try self.checkAssignmentValue(arg.span, ft, ar);
                        }
                        return .{ .ty = try self.allocTy(.{ .adt = aidx }), .range = null };
                    }
                }
            }
        }

        // Handle qualified constructors `Status.Moving(...)` or local closures / function values.
        if (callee.* == .field and callee.field.target.* == .upper_ident) {
            const adt_name = callee.field.target.upper_ident.slice(self.source);
            const var_name = callee.field.name.slice(self.source);
            if (self.findADTIndex(adt_name)) |aidx| {
                for (self.adt_defs.items[aidx].variants) |v| {
                    if (std.mem.eql(u8, v.name, var_name)) {
                        for (args, 0..) |arg, ai| {
                            const exp_ft: ?*const Ty = if (ai < v.field_types.len) v.field_types[ai] else null;
                            const ar = try self.checkExpr(arg.value, exp_ft);
                            if (exp_ft) |ft| try self.checkAssignmentValue(arg.span, ft, ar);
                        }
                        return .{ .ty = try self.allocTy(.{ .adt = aidx }), .range = null };
                    }
                }
                for (args) |arg| _ = try self.checkExpr(arg.value, null);
                return .{ .ty = try self.allocTy(.{ .adt = aidx }), .range = null };
            }
        }

        const callee_res = try self.checkExpr(callee, null);
        if (callee_res.ty.* == .fn_ty) {
            const ft = callee_res.ty.fn_ty;
            if (callee.* == .ident and ft.is_once) {
                if (self.lookupVar(callee.ident.slice(self.source))) |vb| {
                    vb.moved = true;
                }
            }
            const recv_off: usize = if (piped_recv != null) 1 else 0;
            if (piped_recv) |pr| {
                if (ft.params.len > 0) try self.checkAssignmentValue(span, ft.params[0], pr);
            }
            for (args, 0..) |arg, ai| {
                const pidx = ai + recv_off;
                const exp_p: ?*const Ty = if (pidx < ft.params.len) ft.params[pidx] else null;
                const ar = try self.checkExpr(arg.value, exp_p);
                if (exp_p) |ep| {
                    if (!ep.isCopyable() and arg.value.* == .ident) {
                        if (self.lookupVar(arg.value.ident.slice(self.source))) |vb| {
                            if (ep.* != .view and ep.* != .slice and ep.* != .path_borrow) vb.moved = true;
                        }
                    }
                    try self.checkAssignmentValue(arg.span, ep, ar);
                }
            }
            return .{ .ty = ft.ret, .range = ft.ret.rangeOf() };
        }

        for (args) |arg| {
            _ = try self.checkExpr(arg.value, null);
        }
        return .{ .ty = try self.allocTy(.err), .range = null };
    }

    fn combineBinary(
        self: *Analyzer,
        span: ast.Span,
        op: ast.BinaryOp,
        lr: ExprResult,
        rr: ExprResult,
        expected: ?*const Ty,
    ) std.mem.Allocator.Error!ExprResult {
        switch (op) {
            .eq, .ne, .lt, .le, .gt, .ge, .and_op, .or_op => {
                return .{ .ty = try self.allocTy(.bool), .range = null };
            },
            .concat => {
                return .{ .ty = try self.allocTy(.string), .range = null };
            },
            .range, .range_eq => {
                const r1 = lr.range orelse lr.ty.rangeOf();
                const r2 = rr.range orelse rr.ty.rangeOf();
                if (r1 != null and r2 != null) {
                    const jr = r1.?.join(r2.?);
                    if (int_range.inferIntegerType(jr)) |it| {
                        return .{
                            .ty = try self.allocTy(.{ .int_range = .{ .range = jr, .synthesized = it } }),
                            .range = jr,
                        };
                    }
                    return .{ .ty = expected orelse lr.ty, .range = jr };
                }
                return .{ .ty = expected orelse lr.ty, .range = lr.range };
            },
            .add_sat, .sub_sat, .mul_sat, .add_wrap, .sub_wrap, .mul_wrap => {
                // Saturating and wrapping operators are always total: pick lhs integer type or expected!
                const target_ty = if (expected != null and expected.?.isInteger() != null)
                    expected.?
                else if (lr.ty.isInteger() != null)
                    lr.ty
                else
                    rr.ty;
                return .{ .ty = target_ty, .range = target_ty.rangeOf() };
            },
            .add, .sub, .mul, .div, .rem, .bit_or, .bit_xor, .bit_and, .shl, .shr => {
                if (lr.ty.* == .f32 or lr.ty.* == .f64) {
                    return .{ .ty = lr.ty, .range = null };
                }
                const r1 = lr.range orelse lr.ty.rangeOf();
                const r2 = rr.range orelse rr.ty.rangeOf();
                if (r1 != null and r2 != null) {
                    const out_range: ?IntRange = switch (op) {
                        .add => r1.?.add(r2.?),
                        .sub => r1.?.sub(r2.?),
                        .mul => r1.?.mul(r2.?),
                        else => r1.?.join(r2.?),
                    };
                    if (out_range == null) {
                        self.addError(.width_exceeded, span, "arithmetic interval exceeds maximum supported bit width (65535 bits)");
                        return .{ .ty = try self.allocTy(.err), .range = null };
                    }
                    const inferred = int_range.inferIntegerType(out_range.?) orelse {
                        self.addError(.width_exceeded, span, "synthesized integer width exceeds 65535 bits");
                        return .{ .ty = try self.allocTy(.err), .range = null };
                    };
                    return .{
                        .ty = try self.allocTy(.{ .int_range = .{ .range = out_range.?, .synthesized = inferred } }),
                        .range = out_range,
                    };
                }
                return .{ .ty = lr.ty, .range = lr.range };
            },
            .pipe => unreachable,
        }
    }

    fn applyBranchGuard(self: *Analyzer, cond: *const ast.Expr, truthy: bool) std.mem.Allocator.Error!void {
        switch (cond.*) {
            .unary => |u| {
                if (u.op == .not) {
                    try self.applyBranchGuard(u.operand, !truthy);
                }
            },
            .binary => |b| {
                if (b.op == .and_op and truthy) {
                    try self.applyBranchGuard(b.left, true);
                    try self.applyBranchGuard(b.right, true);
                    return;
                }
                if (b.op == .or_op and !truthy) {
                    try self.applyBranchGuard(b.left, false);
                    try self.applyBranchGuard(b.right, false);
                    return;
                }
                if (b.left.* == .ident) {
                    if (evalConstInt(self.source, b.right)) |bound| {
                        const vname = b.left.ident.slice(self.source);
                        if (self.lookupVar(vname)) |vb| {
                            if (vb.range orelse vb.ty.rangeOf()) |cur| {
                                if (if (truthy) b.op else invertCmpOp(b.op)) |effective_op| {
                                    vb.range = narrowByCmp(cur, effective_op, bound) orelse cur;
                                }
                            }
                        }
                    }
                } else if (b.right.* == .ident) {
                    if (evalConstInt(self.source, b.left)) |bound| {
                        const vname = b.right.ident.slice(self.source);
                        if (self.lookupVar(vname)) |vb| {
                            if (vb.range orelse vb.ty.rangeOf()) |cur| {
                                if (flipCmpOp(b.op)) |flipped| {
                                    if (if (truthy) flipped else invertCmpOp(flipped)) |effective_op| {
                                        vb.range = narrowByCmp(cur, effective_op, bound) orelse cur;
                                    }
                                }
                            }
                        }
                    }
                }

                // Record affine order/disequality facts for `AffineIndex` array/slice disjointness.
                const eff_op = if (truthy) b.op else invertCmpOp(b.op) orelse return;
                if (self.extractAffineForm(b.left)) |lf| {
                    if (self.extractAffineForm(b.right)) |rf| {
                        try self.recordRelationalFact(eff_op, lf, rf);
                    }
                }
            },
            else => {},
        }
    }

    fn recordRelationalFact(self: *Analyzer, op: ast.BinaryOp, lf: AffineForm, rf: AffineForm) std.mem.Allocator.Error!void {
        switch (op) {
            .ne => try self.order_facts.append(self.alloc, .{ .lhs = lf, .rhs = rf, .kind = .ne }),
            .lt => {
                try self.order_facts.append(self.alloc, .{ .lhs = lf, .rhs = rf, .kind = .lt });
                if (lf.base != null and rf.base != null and lf.offset >= rf.offset and (lf.offset != 0 or rf.offset != 0)) {
                    try self.order_facts.append(self.alloc, .{
                        .lhs = .{ .base = lf.base, .base_version = lf.base_version, .base_nonneg = lf.base_nonneg, .offset = 0 },
                        .rhs = .{ .base = rf.base, .base_version = rf.base_version, .base_nonneg = rf.base_nonneg, .offset = 0 },
                        .kind = .lt,
                    });
                }
            },
            .le => {
                try self.order_facts.append(self.alloc, .{ .lhs = lf, .rhs = rf, .kind = .le });
                if (lf.base != null and rf.base != null and (lf.offset != 0 or rf.offset != 0)) {
                    if (lf.offset > rf.offset) {
                        try self.order_facts.append(self.alloc, .{
                            .lhs = .{ .base = lf.base, .base_version = lf.base_version, .base_nonneg = lf.base_nonneg, .offset = 0 },
                            .rhs = .{ .base = rf.base, .base_version = rf.base_version, .base_nonneg = rf.base_nonneg, .offset = 0 },
                            .kind = .lt,
                        });
                    } else if (lf.offset == rf.offset) {
                        try self.order_facts.append(self.alloc, .{
                            .lhs = .{ .base = lf.base, .base_version = lf.base_version, .base_nonneg = lf.base_nonneg, .offset = 0 },
                            .rhs = .{ .base = rf.base, .base_version = rf.base_version, .base_nonneg = rf.base_nonneg, .offset = 0 },
                            .kind = .le,
                        });
                    }
                }
            },
            .gt => try self.recordRelationalFact(.lt, rf, lf),
            .ge => try self.recordRelationalFact(.le, rf, lf),
            else => {},
        }
    }

    fn extractAffineForm(self: *Analyzer, expr: *const ast.Expr) ?AffineForm {
        switch (expr.*) {
            .int_lit => |sp| {
                const parsed = int_range.parseIntLiteral(sp.slice(self.source)) orelse return null;
                if (parsed.value > @as(u128, @intCast(std.math.maxInt(i64)))) return null;
                return .{ .base = null, .offset = @intCast(parsed.value) };
            },
            .unary => |u| {
                if (u.op == .neg) {
                    const inner = self.extractAffineForm(u.operand) orelse return null;
                    if (inner.base == null) {
                        return .{ .base = null, .offset = -inner.offset };
                    }
                }
                return null;
            },
            .ident => |sp| {
                const name = sp.slice(self.source);
                if (self.const_map.get(name)) |ce| {
                    if (ce.range) |rng| {
                        if (rng == .bounded and rng.bounded.lo == rng.bounded.hi) {
                            const v = rng.bounded.lo;
                            if (v >= std.math.minInt(i64) and v <= std.math.maxInt(i64)) {
                                return .{ .base = null, .offset = @intCast(v) };
                            }
                        }
                    }
                }
                if (self.lookupVar(name)) |vb| {
                    const nonneg = (if (vb.range) |r| (r == .bounded and r.bounded.lo >= 0) else false) or
                        (if (vb.ty.isInteger()) |it| !it.signed else false);
                    return .{
                        .base = vb.name,
                        .base_version = vb.ssa_version,
                        .base_nonneg = nonneg,
                        .offset = 0,
                    };
                }
                return null;
            },
            .binary => |b| {
                if (b.op == .add or b.op == .add_wrap) {
                    const lf = self.extractAffineForm(b.left) orelse return null;
                    const rf = self.extractAffineForm(b.right) orelse return null;
                    const sum = @addWithOverflow(lf.offset, rf.offset);
                    if (sum[1] != 0) return null;
                    if (lf.base == null) {
                        return .{
                            .base = rf.base,
                            .base_version = rf.base_version,
                            .base_nonneg = rf.base_nonneg,
                            .offset = sum[0],
                        };
                    }
                    if (rf.base == null) {
                        return .{
                            .base = lf.base,
                            .base_version = lf.base_version,
                            .base_nonneg = lf.base_nonneg,
                            .offset = sum[0],
                        };
                    }
                } else if (b.op == .sub or b.op == .sub_wrap) {
                    const lf = self.extractAffineForm(b.left) orelse return null;
                    const rf = self.extractAffineForm(b.right) orelse return null;
                    if (rf.base == null) {
                        const diff = @subWithOverflow(lf.offset, rf.offset);
                        if (diff[1] != 0) return null;
                        return .{
                            .base = lf.base,
                            .base_version = lf.base_version,
                            .base_nonneg = lf.base_nonneg,
                            .offset = diff[0],
                        };
                    }
                }
                return null;
            },
            .field => |fld| {
                if (fld.target.* == .ident and std.mem.eql(u8, fld.name.slice(self.source), "len")) {
                    const rname = fld.target.ident.slice(self.source);
                    if (self.lookupVar(rname)) |vb| {
                        const len_name = std.fmt.allocPrint(self.alloc, "{s}.len", .{rname}) catch return null;
                        return .{
                            .base = len_name,
                            .base_version = vb.ssa_version,
                            .base_nonneg = true,
                            .offset = 0,
                        };
                    }
                }
                return null;
            },
            else => return null,
        }
    }

    fn extractAccessIndex(self: *Analyzer, idx_expr: *const ast.Expr) AccessIndex {
        if (idx_expr.* == .binary and idx_expr.binary.op == .range) {
            if (self.extractAffineForm(idx_expr.binary.left)) |lo| {
                if (self.extractAffineForm(idx_expr.binary.right)) |hi| {
                    return .{ .slice = .{ .lo = lo, .hi = hi } };
                }
            }
            return .unknown;
        }
        if (self.extractAffineForm(idx_expr)) |af| {
            return .{ .elem = af };
        }
        return .unknown;
    }

    fn provesLe(self: *const Analyzer, a: AffineForm, b: AffineForm) bool {
        if (a.base == null and b.base == null) return a.offset <= b.offset;
        if (a.base == null and b.base != null) {
            return b.base_nonneg and a.offset <= b.offset;
        }
        if (a.base == null or b.base == null) return false;
        if (a.eqlVar(b)) return a.offset <= b.offset;
        for (self.order_facts.items) |fact| {
            if (fact.kind == .le and fact.lhs.eqlVar(a) and fact.rhs.eqlVar(b)) {
                const adj_a = a.offset -| fact.lhs.offset;
                const adj_b = b.offset -| fact.rhs.offset;
                if (adj_a <= adj_b) return true;
            } else if (fact.kind == .lt and fact.lhs.eqlVar(a) and fact.rhs.eqlVar(b)) {
                const adj_a = (a.offset -| fact.lhs.offset) -| 1;
                const adj_b = b.offset -| fact.rhs.offset;
                if (adj_a <= adj_b) return true;
            }
        }
        return false;
    }

    fn provesLt(self: *const Analyzer, a: AffineForm, b: AffineForm) bool {
        if (a.base == null and b.base == null) return a.offset < b.offset;
        if (a.base == null and b.base != null) {
            return b.base_nonneg and a.offset < b.offset;
        }
        if (a.base == null or b.base == null) return false;
        if (a.eqlVar(b)) return a.offset < b.offset;
        for (self.order_facts.items) |fact| {
            if (fact.kind == .lt and fact.lhs.eqlVar(a) and fact.rhs.eqlVar(b)) {
                if (a.offset - fact.lhs.offset <= b.offset - fact.rhs.offset) return true;
            } else if (fact.kind == .le and fact.lhs.eqlVar(a) and fact.rhs.eqlVar(b)) {
                if (a.offset - fact.lhs.offset < b.offset - fact.rhs.offset) return true;
            }
        }
        return false;
    }

    fn provesNe(self: *const Analyzer, a: AffineForm, b: AffineForm) bool {
        if (self.provesLt(a, b) or self.provesLt(b, a)) return true;
        for (self.order_facts.items) |fact| {
            if (fact.kind != .ne) continue;
            if (fact.lhs.eqlVar(a) and fact.rhs.eqlVar(b) and (a.offset - fact.lhs.offset == b.offset - fact.rhs.offset)) {
                return true;
            }
            if (fact.lhs.eqlVar(b) and fact.rhs.eqlVar(a) and (b.offset - fact.lhs.offset == a.offset - fact.rhs.offset)) {
                return true;
            }
        }
        return false;
    }

    fn slicesDisjoint(self: *const Analyzer, s1: SymbolicSlice, s2: SymbolicSlice) bool {
        return self.provesLe(s1.hi, s2.lo) or
            self.provesLe(s2.hi, s1.lo) or
            self.provesLe(s1.hi, s1.lo) or
            self.provesLe(s2.hi, s2.lo);
    }

    fn elemDisjointFromSlice(self: *const Analyzer, idx: AffineForm, s: SymbolicSlice) bool {
        return self.provesLt(idx, s.lo) or self.provesLe(s.hi, idx) or self.provesLe(s.hi, s.lo);
    }

    fn accessIndicesDisjoint(self: *Analyzer, a: AccessIndex, b: AccessIndex, record_cert: bool) bool {
        switch (a) {
            .unknown => return false,
            .elem => |ea| switch (b) {
                .unknown => return false,
                .elem => |eb| {
                    if (!self.provesNe(ea, eb)) return false;
                    if (record_cert) self.emitDisjointCert(.{ .idx_ne = .{ .a = ea, .b = eb } });
                    return true;
                },
                .slice => |sb| {
                    if (!self.elemDisjointFromSlice(ea, sb)) return false;
                    if (record_cert) {
                        const s1 = SymbolicSlice{
                            .lo = ea,
                            .hi = .{ .base = ea.base, .base_version = ea.base_version, .base_nonneg = ea.base_nonneg, .offset = ea.offset + 1 },
                        };
                        self.emitDisjointCert(.{ .slice_disjoint = .{ .s1 = s1, .s2 = sb } });
                    }
                    return true;
                },
            },
            .slice => |sa| switch (b) {
                .unknown => return false,
                .elem => |eb| {
                    if (!self.elemDisjointFromSlice(eb, sa)) return false;
                    if (record_cert) {
                        const s2 = SymbolicSlice{
                            .lo = eb,
                            .hi = .{ .base = eb.base, .base_version = eb.base_version, .base_nonneg = eb.base_nonneg, .offset = eb.offset + 1 },
                        };
                        self.emitDisjointCert(.{ .slice_disjoint = .{ .s1 = sa, .s2 = s2 } });
                    }
                    return true;
                },
                .slice => |sb| {
                    if (!self.slicesDisjoint(sa, sb)) return false;
                    if (record_cert) self.emitDisjointCert(.{ .slice_disjoint = .{ .s1 = sa, .s2 = sb } });
                    return true;
                },
            },
        }
    }

    fn emitDisjointCert(self: *Analyzer, kind: DisjointCertEmit.Kind) void {
        if (self.current_disjoint_certs) |list| {
            const snap = self.alloc.dupe(OrderFact, self.order_facts.items) catch return;
            list.append(self.alloc, .{
                .facts = snap,
                .kind = kind,
            }) catch {};
        }
    }

    fn verifyReturnedViewOrigin(self: *Analyzer, span: ast.Span, expr: *const ast.Expr, req_mode: ast.BorrowMode) std.mem.Allocator.Error!void {
        const rn = self.extractRootIdent(expr) orelse {
            self.addError(.borrow_conflict, span, "returned View must be rooted in a caller-borrowed parameter");
            return;
        };
        const vb = self.lookupVar(rn) orelse {
            self.addError(.borrow_conflict, span, "returned View references unknown binding");
            return;
        };
        const is_caller_param_borrow = vb.view_is_caller_rooted or
            (vb.is_param and (vb.ty.* == .path_borrow or vb.ty.* == .view or vb.ty.* == .slice or vb.ty.* == .collection));
        if (!is_caller_param_borrow) {
            self.addError(.borrow_conflict, span, "cannot return View to stack-local variable or by-value parameter (dangling view)");
            return;
        }
        if (req_mode == .exclusive) {
            if ((vb.ty.* == .view and vb.ty.view.mode == .shared) or
                (vb.ty.* == .path_borrow and vb.ty.path_borrow.mode != null and vb.ty.path_borrow.mode.? == .shared) or
                (vb.ty.* == .slice and !vb.ty.slice.mutable))
            {
                self.addError(.borrow_conflict, span, "cannot return Exclusive View derived from a shared parameter");
                return;
            }
        }
        if (self.inferred_return_origin == null) {
            self.inferred_return_origin = vb.param_index;
        }
    }

    fn attachReturnedViewBinding(
        self: *Analyzer,
        vb: *Binding,
        val_expr: *const ast.Expr,
        vty: anytype,
        span: ast.Span,
    ) std.mem.Allocator.Error!void {
        if (val_expr.* == .call and val_expr.call.callee.* == .ident) {
            if (self.findFnIndex(val_expr.call.callee.ident.slice(self.source))) |fidx| {
                const fsig = self.fn_sigs.items[fidx];
                if (fsig.returned_origin) |orig_idx| {
                    if (orig_idx < val_expr.call.args.len) {
                        const arg_expr = val_expr.call.args[orig_idx].value;
                        const resolved = self.resolveAccessRoot(arg_expr);
                        const root_name = resolved.root_name orelse "";
                        const idx_key: ?AccessIndex = resolved.view_index_key orelse if (arg_expr.* == .index)
                            self.extractAccessIndex(arg_expr.index.idx)
                        else
                            null;
                        const init_perm: BorrowPerm = if (vty.mode == .exclusive) .reserved else .shared;
                        const ridx = vty.target_record;

                        for (self.active_views.items) |av| {
                            if (!av.active) continue;
                            if (std.mem.eql(u8, av.root_name, root_name) and root_name.len > 0) {
                                if (av.index_key != null and idx_key != null) {
                                    if (self.accessIndicesDisjoint(av.index_key.?, idx_key.?, true)) continue;
                                }
                                if (fieldsMayOverlap(av.field_idx, null) and !BorrowPerm.compatible(init_perm, av.perm)) {
                                    self.addError(.borrow_conflict, span, "returned View conflicts with active borrow on the same argument");
                                }
                            }
                        }

                        const vid = self.next_view_id;
                        self.next_view_id += 1;
                        const in_trace = (self.branch_depth == 0 and ridx != null and idx_key == null and self.current_perm_trace != null);
                        if (in_trace) {
                            try self.current_perm_trace.?.append(self.alloc, .{ .reserve = .{
                                .view_id = vid,
                                .root_name = root_name,
                                .record_idx = ridx.?,
                                .field_idx = null,
                                .perm = init_perm,
                            } });
                        }
                        try self.active_views.append(self.alloc, .{
                            .id = vid,
                            .binding_name = vb.name,
                            .root_name = root_name,
                            .record_idx = ridx,
                            .field_idx = null,
                            .index_key = idx_key,
                            .perm = init_perm,
                            .active = true,
                            .is_sentinel = false,
                            .in_trace = in_trace,
                        });
                        vb.view_id = vid;
                        vb.view_root = if (root_name.len > 0) root_name else null;
                        vb.view_record_idx = ridx;
                        vb.view_index_key = idx_key;
                        if (self.lookupVar(root_name)) |src_vb| {
                            if (src_vb.view_is_caller_rooted or src_vb.is_param) {
                                vb.view_is_caller_rooted = true;
                                vb.param_index = src_vb.param_index;
                            }
                        }
                    }
                }
            }
        }
    }

    fn propagateArgEffect(
        self: *Analyzer,
        arg_expr: *const ast.Expr,
        ridx: usize,
        fidx: usize,
        is_write: bool,
        span: ast.Span,
    ) std.mem.Allocator.Error!void {
        if (is_write) {
            if (self.extractRootIdent(arg_expr)) |raw_rn| {
                if (self.lookupVar(raw_rn)) |vb| {
                    if (vb.authorized_paths) |auths| {
                        var allowed = false;
                        for (auths) |ai| {
                            if (ai == fidx) {
                                allowed = true;
                                break;
                            }
                        }
                        if (!allowed) {
                            self.addError(.unauthorized_field_access, span, "helper call mutates field disallowed by parameter ~>.{...} contract");
                        }
                    }
                    if (vb.ty.* == .view and vb.ty.view.mode == .shared) {
                        self.addError(.borrow_conflict, span, "cannot pass shared view to function that mutates field");
                    }
                }
            }
        }
        const resolved = self.resolveAccessRoot(arg_expr);
        if (resolved.root_name) |rn| {
            const idx_key: ?AccessIndex = resolved.view_index_key orelse if (arg_expr.* == .index)
                self.extractAccessIndex(arg_expr.index.idx)
            else
                null;
            try self.recordAccess(rn, ridx, fidx, is_write, span, idx_key, resolved.through_view_id);
        }
    }

    const PreAlias = struct {
        name: []const u8,
        param_idx: usize,
        record_idx: ?usize,
        fixed_field: ?usize,
    };

    fn lookupPreAlias(aliases: []const PreAlias, name: []const u8) ?PreAlias {
        var i = aliases.len;
        while (i > 0) {
            i -= 1;
            if (std.mem.eql(u8, aliases[i].name, name)) return aliases[i];
        }
        return null;
    }

    fn resolvePreExprAlias(self: *const Analyzer, expr: *const ast.Expr, aliases: []const PreAlias) ?PreAlias {
        switch (expr.*) {
            .ident => |sp| return lookupPreAlias(aliases, sp.slice(self.source)),
            .index => |ix| {
                if (self.resolvePreExprAlias(ix.target, aliases)) |pa| {
                    return .{ .name = pa.name, .param_idx = pa.param_idx, .record_idx = pa.record_idx, .fixed_field = null };
                }
                return null;
            },
            .field => |fld| {
                if (self.resolvePreExprAlias(fld.target, aliases)) |pa| {
                    if (pa.fixed_field != null) return pa;
                    if (pa.record_idx) |ri| {
                        const fi = self.findRecordField(ri, fld.name.slice(self.source));
                        return .{ .name = pa.name, .param_idx = pa.param_idx, .record_idx = ri, .fixed_field = fi };
                    }
                    return pa;
                }
                return null;
            },
            else => return null,
        }
    }

    fn computeTransitiveCallEffects(self: *Analyzer) std.mem.Allocator.Error!void {
        for (self.module.decls) |decl| {
            if (decl.kind != .fn_decl) continue;
            const fd = decl.kind.fn_decl;
            const fidx = self.findFnIndex(fd.name.slice(self.source)) orelse continue;

            var aliases: std.ArrayList(PreAlias) = .empty;
            for (fd.params, 0..) |p, pi| {
                const pty = self.fn_sigs.items[fidx].params[pi];
                try aliases.append(self.alloc, .{
                    .name = p.name.slice(self.source),
                    .param_idx = pi,
                    .record_idx = recordOfType(pty),
                    .fixed_field = null,
                });
            }
            try self.collectPreEffectsBlock(fidx, &fd.body, &aliases, true);
        }

        const n_fns = self.fn_sigs.items.len;
        var iter: usize = 0;
        while (iter <= n_fns + 1) : (iter += 1) {
            var changed = false;
            var ci: usize = 0;
            while (ci < n_fns) : (ci += 1) {
                const links = self.fn_sigs.items[ci].call_links.items;
                for (links) |link| {
                    if (link.callee_idx == ci) continue;
                    const callee_sig = &self.fn_sigs.items[link.callee_idx];
                    for (callee_sig.param_writes.items) |cw| {
                        if (cw.param_idx == link.callee_param) {
                            const new_eff = ParamFieldEffect{
                                .param_idx = link.caller_param,
                                .record_idx = cw.record_idx,
                                .field_idx = cw.field_idx,
                            };
                            if (!containsParamFieldEffect(self.fn_sigs.items[ci].param_writes.items, new_eff)) {
                                try self.fn_sigs.items[ci].param_writes.append(self.alloc, new_eff);
                                changed = true;
                            }
                        }
                    }
                    for (callee_sig.param_reads.items) |cr| {
                        if (cr.param_idx == link.callee_param) {
                            const new_eff = ParamFieldEffect{
                                .param_idx = link.caller_param,
                                .record_idx = cr.record_idx,
                                .field_idx = cr.field_idx,
                            };
                            if (!containsParamFieldEffect(self.fn_sigs.items[ci].param_reads.items, new_eff)) {
                                try self.fn_sigs.items[ci].param_reads.append(self.alloc, new_eff);
                                changed = true;
                            }
                        }
                    }
                }
            }
            if (!changed) break;
        }
    }

    fn containsParamFieldEffect(slice: []const ParamFieldEffect, eff: ParamFieldEffect) bool {
        for (slice) |x| {
            if (x.param_idx == eff.param_idx and x.record_idx == eff.record_idx and x.field_idx == eff.field_idx) return true;
        }
        return false;
    }

    fn addParamEffect(self: *Analyzer, fidx: usize, eff: ParamFieldEffect, is_write: bool) std.mem.Allocator.Error!void {
        const list = if (is_write) &self.fn_sigs.items[fidx].param_writes else &self.fn_sigs.items[fidx].param_reads;
        if (!containsParamFieldEffect(list.items, eff)) {
            try list.append(self.alloc, eff);
        }
    }

    fn collectPreEffectsBlock(self: *Analyzer, fidx: usize, blk: *const ast.Block, aliases: *std.ArrayList(PreAlias), is_fn_tail: bool) std.mem.Allocator.Error!void {
        const mark = aliases.items.len;
        defer aliases.shrinkRetainingCapacity(mark);
        for (blk.stmts) |*st| {
            try self.collectPreEffectsStmt(fidx, st, aliases);
        }
        if (blk.tail) |tail| {
            try self.collectPreEffectsExpr(fidx, tail, aliases);
            if (is_fn_tail and self.fn_sigs.items[fidx].returned_origin == null and self.fn_sigs.items[fidx].ret.* == .view) {
                if (self.resolvePreExprAlias(tail, aliases.items)) |pa| {
                    self.fn_sigs.items[fidx].returned_origin = pa.param_idx;
                }
            }
        }
    }

    fn collectPreEffectsStmt(self: *Analyzer, fidx: usize, stmt: *const ast.Stmt, aliases: *std.ArrayList(PreAlias)) std.mem.Allocator.Error!void {
        switch (stmt.*) {
            .let_stmt => |ls| {
                try self.collectPreEffectsExpr(fidx, ls.value, aliases);
                if (ls.pattern.* == .ident) {
                    if (self.resolvePreExprAlias(ls.value, aliases.items)) |pa| {
                        try aliases.append(self.alloc, .{
                            .name = ls.pattern.ident.name.slice(self.source),
                            .param_idx = pa.param_idx,
                            .record_idx = pa.record_idx,
                            .fixed_field = pa.fixed_field,
                        });
                    }
                }
            },
            .use_stmt => |us| try self.collectPreEffectsExpr(fidx, us.expr, aliases),
            .assign_stmt => |asg| {
                if (asg.target.* == .field) {
                    if (self.resolvePreExprAlias(asg.target.field.target, aliases.items)) |pa| {
                        if (pa.record_idx) |ridx| {
                            if (self.findRecordField(ridx, asg.target.field.name.slice(self.source))) |fi| {
                                try self.addParamEffect(fidx, .{ .param_idx = pa.param_idx, .record_idx = ridx, .field_idx = fi }, true);
                            }
                        }
                    }
                } else {
                    try self.collectPreEffectsExpr(fidx, asg.target, aliases);
                }
                try self.collectPreEffectsExpr(fidx, asg.value, aliases);
            },
            .return_stmt => |rs| {
                if (rs.value) |v| {
                    try self.collectPreEffectsExpr(fidx, v, aliases);
                    if (self.fn_sigs.items[fidx].returned_origin == null and self.fn_sigs.items[fidx].ret.* == .view) {
                        if (self.resolvePreExprAlias(v, aliases.items)) |pa| {
                            self.fn_sigs.items[fidx].returned_origin = pa.param_idx;
                        }
                    }
                }
            },
            .while_stmt => |ws| {
                try self.collectPreEffectsExpr(fidx, ws.cond, aliases);
                try self.collectPreEffectsBlock(fidx, &ws.body, aliases, false);
            },
            .for_stmt => |fs| {
                try self.collectPreEffectsExpr(fidx, fs.iter, aliases);
                try self.collectPreEffectsBlock(fidx, &fs.body, aliases, false);
            },
            .expr_stmt => |es| try self.collectPreEffectsExpr(fidx, es.expr, aliases),
        }
    }

    fn collectPreEffectsExpr(self: *Analyzer, fidx: usize, expr: *const ast.Expr, aliases: *std.ArrayList(PreAlias)) std.mem.Allocator.Error!void {
        switch (expr.*) {
            .unary => |u| try self.collectPreEffectsExpr(fidx, u.operand, aliases),
            .binary => |b| {
                if (b.op == .pipe and b.right.* == .call and b.right.call.callee.* == .ident) {
                    const cname = b.right.call.callee.ident.slice(self.source);
                    if (std.mem.eql(u8, cname, "map_in_place") and b.right.call.args.len == 1 and b.right.call.args[0].value.* == .lambda) {
                        const lam = b.right.call.args[0].value.lambda;
                        if (self.resolvePreExprAlias(b.left, aliases.items)) |pa| {
                            const mark = aliases.items.len;
                            defer aliases.shrinkRetainingCapacity(mark);
                            if (lam.params.len > 0) {
                                try aliases.append(self.alloc, .{
                                    .name = lam.params[0].name.slice(self.source),
                                    .param_idx = pa.param_idx,
                                    .record_idx = pa.record_idx,
                                    .fixed_field = null,
                                });
                            }
                            try self.collectPreEffectsBlock(fidx, &lam.body, aliases, false);
                            return;
                        }
                    } else if (self.findFnIndex(cname)) |callee_idx| {
                        if (self.resolvePreExprAlias(b.left, aliases.items)) |pa| {
                            try self.fn_sigs.items[fidx].call_links.append(self.alloc, .{
                                .caller_param = pa.param_idx,
                                .callee_idx = callee_idx,
                                .callee_param = 0,
                            });
                        }
                        for (b.right.call.args, 0..) |arg, ai| {
                            if (self.resolvePreExprAlias(arg.value, aliases.items)) |pa| {
                                try self.fn_sigs.items[fidx].call_links.append(self.alloc, .{
                                    .caller_param = pa.param_idx,
                                    .callee_idx = callee_idx,
                                    .callee_param = ai + 1,
                                });
                            }
                            try self.collectPreEffectsExpr(fidx, arg.value, aliases);
                        }
                        try self.collectPreEffectsExpr(fidx, b.left, aliases);
                        return;
                    }
                }
                try self.collectPreEffectsExpr(fidx, b.left, aliases);
                try self.collectPreEffectsExpr(fidx, b.right, aliases);
            },
            .cast => |c| try self.collectPreEffectsExpr(fidx, c.expr, aliases),
            .call => |c| {
                if (c.callee.* == .ident) {
                    if (self.findFnIndex(c.callee.ident.slice(self.source))) |callee_idx| {
                        for (c.args, 0..) |arg, ai| {
                            if (self.resolvePreExprAlias(arg.value, aliases.items)) |pa| {
                                try self.fn_sigs.items[fidx].call_links.append(self.alloc, .{
                                    .caller_param = pa.param_idx,
                                    .callee_idx = callee_idx,
                                    .callee_param = ai,
                                });
                            }
                        }
                    }
                }
                for (c.args) |arg| try self.collectPreEffectsExpr(fidx, arg.value, aliases);
            },
            .field => |fld| {
                if (self.resolvePreExprAlias(fld.target, aliases.items)) |pa| {
                    if (pa.record_idx) |ridx| {
                        if (self.findRecordField(ridx, fld.name.slice(self.source))) |fi| {
                            try self.addParamEffect(fidx, .{ .param_idx = pa.param_idx, .record_idx = ridx, .field_idx = fi }, false);
                        }
                    }
                }
                try self.collectPreEffectsExpr(fidx, fld.target, aliases);
            },
            .index => |ix| {
                try self.collectPreEffectsExpr(fidx, ix.target, aliases);
                try self.collectPreEffectsExpr(fidx, ix.idx, aliases);
            },
            .block => |*blk| try self.collectPreEffectsBlock(fidx, blk, aliases, false),
            .if_expr => |ie| {
                try self.collectPreEffectsExpr(fidx, ie.cond, aliases);
                try self.collectPreEffectsBlock(fidx, &ie.then_block, aliases, false);
                if (ie.else_branch) |eb| try self.collectPreEffectsExpr(fidx, eb, aliases);
            },
            .case_expr => |ce| {
                for (ce.subjects) |s| try self.collectPreEffectsExpr(fidx, s, aliases);
                for (ce.arms) |arm| try self.collectPreEffectsExpr(fidx, arm.body, aliases);
            },
            .view_expr => |vw| {
                try self.collectPreEffectsExpr(fidx, vw.target, aliases);
                const mark = aliases.items.len;
                defer aliases.shrinkRetainingCapacity(mark);
                if (vw.binding) |bspan| {
                    if (self.resolvePreExprAlias(vw.target, aliases.items)) |pa| {
                        try aliases.append(self.alloc, .{
                            .name = bspan.slice(self.source),
                            .param_idx = pa.param_idx,
                            .record_idx = pa.record_idx,
                            .fixed_field = pa.fixed_field,
                        });
                    }
                }
                try self.collectPreEffectsBlock(fidx, &vw.body, aliases, false);
            },
            .fork_expr => |fk| {
                for (fk.branches) |*br| try self.collectPreEffectsBlock(fidx, br, aliases, false);
            },
            else => {},
        }
    }

    fn blockMentionsIdent(self: *const Analyzer, blk: *const ast.Block, name: []const u8) bool {
        if (blk.tail) |t| {
            if (self.exprMentionsIdent(t, name)) return true;
        }
        for (blk.stmts) |*st| {
            if (self.stmtMentionsIdent(st, name)) return true;
        }
        return false;
    }

    fn lastUseStmtInBlock(self: *const Analyzer, blk: *const ast.Block, name: []const u8) ?usize {
        if (blk.tail) |t| {
            if (self.exprMentionsIdent(t, name)) return null;
        }
        var last: ?usize = null;
        for (blk.stmts, 0..) |*st, idx| {
            if (self.stmtMentionsIdent(st, name)) last = idx;
            if (st.* == .let_stmt and st.let_stmt.pattern.* == .ident) {
                if (std.mem.eql(u8, st.let_stmt.pattern.ident.name.slice(self.source), name)) break;
            }
        }
        return last;
    }

    fn lastUseStmtAfter(self: *const Analyzer, blk: *const ast.Block, decl_idx: usize, name: []const u8) ?usize {
        if (blk.tail) |t| {
            if (self.exprMentionsIdent(t, name)) return null;
        }
        var last: ?usize = null;
        var idx = decl_idx + 1;
        while (idx < blk.stmts.len) : (idx += 1) {
            const st = &blk.stmts[idx];
            if (self.stmtMentionsIdent(st, name)) last = idx;
            if (st.* == .let_stmt and st.let_stmt.pattern.* == .ident) {
                if (std.mem.eql(u8, st.let_stmt.pattern.ident.name.slice(self.source), name)) break;
            }
        }
        return last;
    }

    fn stmtMentionsIdent(self: *const Analyzer, stmt: *const ast.Stmt, name: []const u8) bool {
        return switch (stmt.*) {
            .let_stmt => |ls| self.exprMentionsIdent(ls.value, name),
            .use_stmt => |us| self.exprMentionsIdent(us.expr, name),
            .assign_stmt => |asg| self.exprMentionsIdent(asg.target, name) or self.exprMentionsIdent(asg.value, name),
            .return_stmt => |rs| if (rs.value) |v| self.exprMentionsIdent(v, name) else false,
            .while_stmt => |ws| self.exprMentionsIdent(ws.cond, name) or self.blockMentionsIdent(&ws.body, name),
            .for_stmt => |fs| self.exprMentionsIdent(fs.iter, name) or self.blockMentionsIdent(&fs.body, name),
            .expr_stmt => |es| self.exprMentionsIdent(es.expr, name),
        };
    }

    fn exprMentionsIdent(self: *const Analyzer, expr: *const ast.Expr, name: []const u8) bool {
        return switch (expr.*) {
            .ident => |sp| std.mem.eql(u8, sp.slice(self.source), name),
            .unary => |u| self.exprMentionsIdent(u.operand, name),
            .binary => |b| self.exprMentionsIdent(b.left, name) or self.exprMentionsIdent(b.right, name),
            .cast => |c| self.exprMentionsIdent(c.expr, name),
            .call => |c| blk: {
                if (self.exprMentionsIdent(c.callee, name)) break :blk true;
                for (c.args) |a| {
                    if (self.exprMentionsIdent(a.value, name)) break :blk true;
                }
                break :blk false;
            },
            .field => |fld| self.exprMentionsIdent(fld.target, name),
            .index => |ix| self.exprMentionsIdent(ix.target, name) or self.exprMentionsIdent(ix.idx, name),
            .try_op => |t| self.exprMentionsIdent(t.operand, name),
            .record_lit => |rl| blk: {
                for (rl.fields) |rf| {
                    if (rf.value) |v| {
                        if (self.exprMentionsIdent(v, name)) break :blk true;
                    } else if (std.mem.eql(u8, rf.name.slice(self.source), name)) {
                        break :blk true;
                    }
                }
                break :blk false;
            },
            .tuple => |tp| blk: {
                for (tp.elems) |el| if (self.exprMentionsIdent(el, name)) break :blk true;
                break :blk false;
            },
            .list => |ls| blk: {
                for (ls.elems) |el| if (self.exprMentionsIdent(el, name)) break :blk true;
                break :blk false;
            },
            .block => |*blk| self.blockMentionsIdent(blk, name),
            .if_expr => |ie| self.exprMentionsIdent(ie.cond, name) or
                self.blockMentionsIdent(&ie.then_block, name) or
                (if (ie.else_branch) |eb| self.exprMentionsIdent(eb, name) else false),
            .case_expr => |ce| blk: {
                for (ce.subjects) |s| if (self.exprMentionsIdent(s, name)) break :blk true;
                for (ce.arms) |arm| {
                    if (arm.guard) |g| if (self.exprMentionsIdent(g, name)) break :blk true;
                    if (self.exprMentionsIdent(arm.body, name)) break :blk true;
                }
                break :blk false;
            },
            .lambda => |lam| self.blockMentionsIdent(&lam.body, name),
            .view_expr => |vw| self.exprMentionsIdent(vw.target, name) or self.blockMentionsIdent(&vw.body, name),
            .fork_expr => |fk| blk: {
                for (fk.branches) |*br| if (self.blockMentionsIdent(br, name)) break :blk true;
                break :blk false;
            },
            .todo_expr => |td| if (td.message) |m| self.exprMentionsIdent(m, name) else false,
            .panic_expr => |pn| if (pn.message) |m| self.exprMentionsIdent(m, name) else false,
            else => false,
        };
    }

    fn invertCmpOp(op: ast.BinaryOp) ?ast.BinaryOp {
        return switch (op) {
            .lt => .ge,
            .le => .gt,
            .gt => .le,
            .ge => .lt,
            .eq => .ne,
            .ne => .eq,
            else => null,
        };
    }

    fn flipCmpOp(op: ast.BinaryOp) ?ast.BinaryOp {
        return switch (op) {
            .lt => .gt,
            .le => .ge,
            .gt => .lt,
            .ge => .le,
            .eq => .eq,
            .ne => .ne,
            else => null,
        };
    }

    fn narrowByCmp(cur: IntRange, op: ast.BinaryOp, bound: i128) ?IntRange {
        return switch (op) {
            .le => cur.narrowUpper(bound),
            .lt => if (bound > std.math.minInt(i128)) cur.narrowUpper(bound - 1) else null,
            .ge => cur.narrowLower(bound),
            .gt => if (bound < std.math.maxInt(i128)) cur.narrowLower(bound + 1) else null,
            .eq => if (cur.narrowLower(bound)) |c1| c1.narrowUpper(bound) else null,
            .ne => if (cur == .bounded and cur.bounded.lo == bound and cur.bounded.lo < cur.bounded.hi)
                cur.narrowLower(bound + 1)
            else if (cur == .bounded and cur.bounded.hi == bound and cur.bounded.lo < cur.bounded.hi)
                cur.narrowUpper(bound - 1)
            else
                null,
            else => null,
        };
    }

    fn markHotFieldsSince(self: *Analyzer, ridx: usize, acc_start: usize) void {
        if (self.current_accesses) |al| {
            for (al.items[acc_start..]) |acc| {
                if (acc.record_idx != null and acc.record_idx.? == ridx and acc.field_idx != null) {
                    const fi = acc.field_idx.?;
                    if (fi < self.record_defs.items[ridx].hot_fields.len) {
                        self.record_defs.items[ridx].hot_fields[fi] = true;
                    }
                }
            }
        }
    }

    fn isSimdFieldTy(ty: *const Ty) bool {
        return switch (ty.*) {
            .f32, .f64 => true,
            .int => |it| it.bits == 8 or it.bits == 16 or it.bits == 32 or it.bits == 64,
            .int_range => |ir| ir.synthesized.bits == 8 or ir.synthesized.bits == 16 or ir.synthesized.bits == 32 or ir.synthesized.bits == 64,
            else => false,
        };
    }

    fn isSimdVectorExpr(self: *const Analyzer, ridx: usize, elem_param: []const u8, expr: *const ast.Expr) bool {
        return switch (expr.*) {
            .int_lit, .float_lit => true,
            .ident => |sp| !std.mem.eql(u8, sp.slice(self.source), elem_param),
            .unary => |u| (u.op == .neg) and self.isSimdVectorExpr(ridx, elem_param, u.operand),
            .binary => |b| switch (b.op) {
                .add, .sub, .mul, .div => self.isSimdVectorExpr(ridx, elem_param, b.left) and
                    self.isSimdVectorExpr(ridx, elem_param, b.right),
                else => false,
            },
            .field => |fld| blk: {
                if (fld.target.* != .ident) break :blk false;
                if (!std.mem.eql(u8, fld.target.ident.slice(self.source), elem_param)) break :blk false;
                const fi = self.findRecordField(ridx, fld.name.slice(self.source)) orelse break :blk false;
                break :blk isSimdFieldTy(self.record_defs.items[ridx].fields[fi].ty);
            },
            .cast => |c| self.isSimdVectorExpr(ridx, elem_param, c.expr),
            else => false,
        };
    }

    fn isSimdVectorizableLambda(self: *const Analyzer, ridx: usize, elem_param: []const u8, body: *const ast.Block) bool {
        if (body.tail != null or body.stmts.len == 0) return false;
        var has_field_write = false;
        for (body.stmts) |st| {
            switch (st) {
                .let_stmt => |ls| {
                    if (ls.pattern.* != .ident) return false;
                    if (!self.isSimdVectorExpr(ridx, elem_param, ls.value)) return false;
                },
                .assign_stmt => |asg| {
                    switch (asg.op) {
                        .assign, .add_assign, .sub_assign, .mul_assign, .div_assign => {},
                        else => return false,
                    }
                    if (!self.isSimdVectorExpr(ridx, elem_param, asg.value)) return false;
                    if (asg.target.* == .field) {
                        const fld = asg.target.field;
                        if (fld.target.* != .ident) return false;
                        if (!std.mem.eql(u8, fld.target.ident.slice(self.source), elem_param)) return false;
                        const fi = self.findRecordField(ridx, fld.name.slice(self.source)) orelse return false;
                        if (!isSimdFieldTy(self.record_defs.items[ridx].fields[fi].ty)) return false;
                        has_field_write = true;
                    } else if (asg.target.* != .ident) {
                        return false;
                    }
                },
                else => return false,
            }
        }
        return has_field_write;
    }

    fn synthesizeAllLayouts(self: *Analyzer) std.mem.Allocator.Error![]CheckedRecord {
        const out = try self.alloc.alloc(CheckedRecord, self.record_defs.items.len);
        for (self.record_defs.items, 0..) |*rdef, ridx| {
            const schemas = try self.alloc.alloc(layout.FieldSchema, rdef.fields.len);
            for (rdef.fields, 0..) |f, fi| {
                const info = self.typeBitInfo(f.ty);
                schemas[fi] = .{
                    .name = f.name,
                    .bits = @max(@as(u16, 1), info.bits),
                    .signed = info.signed,
                    .addressable_size = info.size,
                    .addressable_align = info.alignment,
                    .is_subbyte_packable = info.packable,
                };
            }
            const base_planned = try layout.planRecordLayout(self.alloc, schemas, rdef.conflicts.items);

            var hot_count: usize = 0;
            var hot_bytes: usize = 0;
            for (rdef.hot_fields, 0..) |is_h, fi| {
                if (is_h) {
                    hot_count += 1;
                    hot_bytes += @max(@as(usize, 1), schemas[fi].addressable_size);
                }
            }

            var auto_decision: ?layout.AutoLayoutDecision = null;
            if (rdef.auto_layout_requested) {
                const decision = layout.selectAutoCollectionLayout(.{
                    .total_record_bytes = @max(@as(usize, 1), base_planned.size),
                    .hot_record_bytes = hot_bytes,
                    .hot_field_count = hot_count,
                    .total_field_count = rdef.fields.len,
                    .has_simd_loop = rdef.simd_loop_seen,
                    .observed_len = rdef.observed_collection_len,
                });
                auto_decision = decision;
                rdef.collection_layout = decision.selected;
            }

            var final_planned = base_planned;
            if (hot_count > 0 and hot_count < rdef.fields.len and rdef.fields.len > 1) {
                const orig_indices = try self.alloc.alloc(usize, rdef.fields.len);
                for (orig_indices, 0..) |*idx_slot, fi| idx_slot.* = fi;
                const reordered_idx = try layout.reorderHotFieldsFirst(usize, self.alloc, orig_indices, rdef.hot_fields);
                const pos_of = try self.alloc.alloc(usize, rdef.fields.len);
                const reordered_schemas = try self.alloc.alloc(layout.FieldSchema, rdef.fields.len);
                for (reordered_idx, 0..) |orig_fi, new_pos| {
                    pos_of[orig_fi] = new_pos;
                    reordered_schemas[new_pos] = schemas[orig_fi];
                }
                const remapped_conflicts = try self.alloc.alloc(layout.ConflictPair, rdef.conflicts.items.len);
                for (rdef.conflicts.items, 0..) |cp, ci| {
                    remapped_conflicts[ci] = .{ .a = pos_of[cp.a], .b = pos_of[cp.b] };
                }
                const reordered_planned = try layout.planRecordLayout(self.alloc, reordered_schemas, remapped_conflicts);
                const restored_fields = try self.alloc.alloc(layout.FieldPlacement, rdef.fields.len);
                for (reordered_idx, 0..) |orig_fi, new_pos| {
                    restored_fields[orig_fi] = reordered_planned.fields[new_pos];
                }
                final_planned = .{
                    .size = reordered_planned.size,
                    .alignment = reordered_planned.alignment,
                    .fields = restored_fields,
                };
            }

            out[ridx] = .{
                .name = rdef.name,
                .span = rdef.span,
                .fields = rdef.fields,
                .conflicts = try rdef.conflicts.toOwnedSlice(self.alloc),
                .record_layout = final_planned,
                .collection_layout = rdef.collection_layout,
                .hot_fields = rdef.hot_fields,
                .auto_layout_decision = auto_decision,
            };
            if (rdef.collection_layout) |cl| {
                if (!self.hasCollectionNamed(rdef.name)) {
                    try self.checked_collections.append(self.alloc, .{
                        .name = rdef.name,
                        .layout = cl,
                        .field_count = @max(@as(usize, 1), rdef.fields.len),
                    });
                }
            }
        }
        return out;
    }

    fn hasCollectionNamed(self: *const Analyzer, name: []const u8) bool {
        for (self.checked_collections.items) |c| {
            if (std.mem.eql(u8, c.name, name)) return true;
        }
        return false;
    }

    fn invertCondExpr(self: *Analyzer, cond: *const ast.Expr) std.mem.Allocator.Error!*const ast.Expr {
        if (cond.* == .binary) {
            const b = cond.binary;
            if (invertCmpOp(b.op)) |inv_op| {
                const ptr = try self.alloc.create(ast.Expr);
                ptr.* = .{ .binary = .{
                    .span = b.span,
                    .op = inv_op,
                    .left = b.left,
                    .right = b.right,
                } };
                return ptr;
            }
        }
        const ptr = try self.alloc.create(ast.Expr);
        ptr.* = .{ .unary = .{
            .span = cond.getSpan(),
            .op = .not,
            .operand = cond,
        } };
        return ptr;
    }

    fn isTyNonNegativeNat(ty: *const Ty) ?struct { non_neg: bool, lower: ?u64 } {
        return switch (ty.*) {
            .int => |it| if (!it.signed) .{ .non_neg = true, .lower = null } else .{ .non_neg = false, .lower = null },
            .int_range => |ir| switch (ir.range) {
                .bounded => |b| if (b.lo >= 0) .{
                    .non_neg = true,
                    .lower = if (b.lo <= std.math.maxInt(u64)) @intCast(b.lo) else null,
                } else .{ .non_neg = false, .lower = null },
                else => .{ .non_neg = false, .lower = null },
            },
            else => null,
        };
    }

    fn collectSymBindingsFromScopes(self: *const Analyzer) std.mem.Allocator.Error![]const law_verifier.SymBinding {
        var out: std.ArrayList(law_verifier.SymBinding) = .empty;
        for (self.scopes.items) |sb| {
            if (isTyNonNegativeNat(sb.ty)) |nn| {
                const eff_lo: ?u64 = blk: {
                    if (sb.range) |r| {
                        if (r == .bounded and r.bounded.lo > 0 and r.bounded.lo <= std.math.maxInt(u64)) {
                            break :blk @intCast(r.bounded.lo);
                        }
                    }
                    break :blk nn.lower;
                };
                try out.append(self.alloc, .{
                    .name = sb.name,
                    .non_negative = nn.non_neg,
                    .min_lower_bound = eff_lo,
                });
            } else {
                try out.append(self.alloc, .{ .name = sb.name, .non_negative = false, .min_lower_bound = null });
            }
            if (recordOfType(sb.ty)) |ridx| {
                const rdef = self.record_defs.items[ridx];
                for (rdef.fields) |rf| {
                    if (isTyNonNegativeNat(rf.ty)) |nn| {
                        const key = try std.fmt.allocPrint(self.alloc, "{s}.{s}", .{ sb.name, rf.name });
                        try out.append(self.alloc, .{
                            .name = key,
                            .non_negative = nn.non_neg,
                            .min_lower_bound = nn.lower,
                        });
                    }
                }
            }
        }
        return try out.toOwnedSlice(self.alloc);
    }

    fn collectModuleFnAsts(self: *const Analyzer) std.mem.Allocator.Error![]const law_verifier.FnAstEntry {
        var list: std.ArrayList(law_verifier.FnAstEntry) = .empty;
        for (self.module.decls) |decl| {
            if (decl.kind == .fn_decl) {
                const fd = decl.kind.fn_decl;
                try list.append(self.alloc, .{
                    .name = fd.name.slice(self.source),
                    .params = fd.params,
                    .body = fd.body,
                });
            }
        }
        return try list.toOwnedSlice(self.alloc);
    }

    fn collectRecordAstInfos(self: *const Analyzer) std.mem.Allocator.Error![]const law_verifier.RecordAstInfo {
        var list: std.ArrayList(law_verifier.RecordAstInfo) = .empty;
        for (self.record_defs.items) |rdef| {
            var fs = try self.alloc.alloc(law_verifier.RecordFieldRuntime, rdef.fields.len);
            for (rdef.fields, 0..) |rf, fi| {
                fs[fi] = .{
                    .name = rf.name,
                    .int_ty = rf.ty.isInteger(),
                    .is_bool = rf.ty.* == .bool,
                };
            }
            try list.append(self.alloc, .{ .name = rdef.name, .fields = fs });
        }
        return try list.toOwnedSlice(self.alloc);
    }

    fn tyToParamDomain(self: *const Analyzer, name: []const u8, ty: *const Ty) std.mem.Allocator.Error!law_verifier.LawParamDomain {
        const inner = if (ty.* == .view) ty.view.target else ty;
        switch (inner.*) {
            .bool => return .{ .name = name, .kind = .bool_ty },
            .int => |it| return .{ .name = name, .kind = .{ .int_ty = .{ .int_ty = it, .range = inner.rangeOf() } } },
            .int_range => |ir| return .{ .name = name, .kind = .{ .int_ty = .{ .int_ty = ir.synthesized, .range = ir.range } } },
            .record => |ridx| {
                const rdef = self.record_defs.items[ridx];
                var fs = try self.alloc.alloc(law_verifier.ParamFieldInfo, rdef.fields.len);
                for (rdef.fields, 0..) |rf, fi| {
                    fs[fi] = .{
                        .name = rf.name,
                        .int_ty = rf.ty.isInteger(),
                        .range = rf.ty.rangeOf(),
                        .is_bool = rf.ty.* == .bool,
                    };
                }
                return .{ .name = name, .kind = .{ .record_ty = .{ .record_name = rdef.name, .fields = fs } } };
            },
            .adt => |aidx| {
                const adef = self.adt_defs.items[aidx];
                var all_unit = true;
                for (adef.variants) |v| {
                    if (v.field_types.len > 0) {
                        all_unit = false;
                        break;
                    }
                }
                if (all_unit) {
                    return .{ .name = name, .kind = .{ .enum_ty = .{ .adt_name = adef.name, .variant_count = adef.variants.len } } };
                }
                return .{ .name = name, .kind = .other };
            },
            else => return .{ .name = name, .kind = .other },
        }
    }

    fn verifyWhileDecreasesStmt(
        self: *Analyzer,
        span: ast.Span,
        cond: *const ast.Expr,
        dec: *const ast.Expr,
        body: ast.Block,
    ) std.mem.Allocator.Error!void {
        const bindings = try self.collectSymBindingsFromScopes();
        const fn_asts = try self.collectModuleFnAsts();
        switch (law_verifier.verifyWhileDecreases(self.alloc, self.source, fn_asts, cond, dec, body, bindings)) {
            .proved => |cert| {
                if (self.current_decreases_certs) |list| {
                    try list.append(self.alloc, cert);
                }
            },
            .failed => |reason| {
                self.addError(.termination_error, span, reason);
            },
        }
    }

    fn verifyRecursiveDecreasesCall(
        self: *Analyzer,
        span: ast.Span,
        arg_exprs: []const *const ast.Expr,
    ) std.mem.Allocator.Error!void {
        const dec = self.current_fn_decreases orelse return;
        const bindings = try self.collectSymBindingsFromScopes();
        const fn_asts = try self.collectModuleFnAsts();
        switch (law_verifier.verifyRecursiveCallDecreases(
            self.alloc,
            self.source,
            fn_asts,
            self.current_sym_guards.items,
            dec,
            self.current_fn_params,
            arg_exprs,
            bindings,
        )) {
            .proved => |cert| {
                if (self.current_decreases_certs) |list| {
                    try list.append(self.alloc, cert);
                }
            },
            .failed => |reason| {
                self.addError(.termination_error, span, reason);
            },
        }
    }

    fn checkLaws(self: *Analyzer, checked_records: []const CheckedRecord) std.mem.Allocator.Error!void {
        _ = checked_records;
        const fn_asts = try self.collectModuleFnAsts();
        const rec_infos = try self.collectRecordAstInfos();

        for (self.module.decls) |decl| {
            if (decl.kind != .law_decl) continue;
            const ld = decl.kind.law_decl;
            const lname = ld.name.slice(self.source);

            try self.pushScope();
            defer self.popScope();

            var law_rec_idx: ?usize = null;
            var param_domains = try self.alloc.alloc(law_verifier.LawParamDomain, ld.params.len);
            for (ld.params, 0..) |p, pi| {
                const pty = if (p.ty) |t| try self.resolveType(t) else try self.allocTy(.err);
                const pname = p.name.slice(self.source);
                if (law_rec_idx == null) law_rec_idx = recordOfType(pty);
                param_domains[pi] = try self.tyToParamDomain(pname, pty);
                try self.scopes.append(self.alloc, .{
                    .name = pname,
                    .ty = pty,
                    .range = pty.rangeOf(),
                    .mutable = p.mutable,
                    .moved = false,
                    .authorized_paths = null,
                    .decl_span = p.span,
                });
            }

            const sym_bindings = try self.collectSymBindingsFromScopes();
            var sym_ctx = law_verifier.SymCtx{
                .alloc = self.alloc,
                .source = self.source,
                .fns = fn_asts,
            };
            for (sym_bindings) |sb| _ = sym_ctx.bindVar(sb.name, sb.non_negative);

            var guards_ast: std.ArrayList(*const ast.Expr) = .empty;
            var sym_certs: std.ArrayList(law_verifier.SymbolicLawCert) = .empty;
            var has_symbolic_guard = false;
            var has_claim = false;
            var all_proved = ld.clauses.len > 0;
            var violated = false;
            var falsified = false;
            var tier0_ok = false;
            var tier1_ok = false;
            var tier2_ok = false;
            var interval_ok = false;
            var tier1_max_states: usize = 0;
            var first_counterexample: ?[]const u8 = null;

            for (ld.clauses, 0..) |cl, ci| {
                switch (cl) {
                    .preserves => |pr| {
                        has_claim = true;
                        for (pr.paths) |fp| {
                            if (fp.len < 2) continue;
                            const pname = fp[0].slice(self.source);
                            const fname = fp[1].slice(self.source);
                            const vb = self.lookupVar(pname) orelse continue;
                            const ridx = recordOfType(vb.ty) orelse continue;
                            const fidx = self.findRecordField(ridx, fname) orelse {
                                self.addError(.law_violation, fp[1], "preserved field does not exist on record");
                                violated = true;
                                continue;
                            };
                            // Tier 0: verify no checked function operating on `ridx` writes `fidx`, and attach `fidx` to `preserves`.
                            for (self.checked_functions.items) |*cf| {
                                if (cf.target_record != null and cf.target_record.? == ridx) {
                                    var writes_preserved = false;
                                    for (cf.writes) |w| {
                                        if (w.record_idx == ridx and w.field_idx == fidx) {
                                            writes_preserved = true;
                                            break;
                                        }
                                    }
                                    if (writes_preserved) {
                                        self.addError(.law_violation, fp[1], "constitutional law violation: function mutates preserved field");
                                        violated = true;
                                    } else {
                                        var updated: std.ArrayList(usize) = .empty;
                                        for (cf.preserves) |prev| try updated.append(self.alloc, prev);
                                        var dup = false;
                                        for (updated.items) |u| if (u == fidx) {
                                            dup = true;
                                        };
                                        if (!dup) try updated.append(self.alloc, fidx);
                                        cf.preserves = try updated.toOwnedSlice(self.alloc);
                                    }
                                }
                            }
                        }
                        if (!violated) tier0_ok = true;
                    },
                    .when => |wh| {
                        _ = try self.checkExpr(wh.expr, try self.allocTy(.bool));
                        try self.applyBranchGuard(wh.expr, true);
                        try guards_ast.append(self.alloc, wh.expr);
                        if (wh.expr.* == .binary) {
                            const wb = wh.expr.binary;
                            if (evalConstInt(self.source, wb.left) == null and evalConstInt(self.source, wb.right) == null) {
                                has_symbolic_guard = true;
                            }
                        }
                    },
                    .always, .never, .expr => {
                        has_claim = true;
                        const is_never = (cl == .never);
                        const cl_span = switch (cl) {
                            .always => |a| a.span,
                            .never => |n| n.span,
                            .expr => |e| e.span,
                            else => unreachable,
                        };
                        const goal_expr = switch (cl) {
                            .always => |a| a.expr,
                            .never => |n| n.expr,
                            .expr => |e| e.expr,
                            else => unreachable,
                        };
                        _ = try self.checkExpr(goal_expr, try self.allocTy(.bool));

                        const itruth = try self.evalIntervalPredicate(goal_expr, has_symbolic_guard);
                        const interval_proved = (is_never and itruth == .always_false) or (!is_never and itruth == .always_true);
                        if (interval_proved) {
                            interval_ok = true;
                            continue;
                        }

                        if (law_verifier.tryProveSymbolicClause(self.alloc, &sym_ctx, guards_ast.items, goal_expr, is_never)) |sym_ok| {
                            tier2_ok = true;
                            const cert_name = if (ld.clauses.len <= 1)
                                lname
                            else
                                try std.fmt.allocPrint(self.alloc, "{s}__c{d}", .{ lname, ci });
                            try sym_certs.append(self.alloc, .{
                                .name = cert_name,
                                .kind = if (is_never) .never else .always,
                                .hyps = sym_ok.hyps,
                                .goal = sym_ok.goal,
                            });
                            continue;
                        }

                        switch (law_verifier.runTier1Clause(self.alloc, self.source, fn_asts, rec_infos, param_domains, guards_ast.items, goal_expr, is_never)) {
                            .proved_exhaustive => |states| {
                                tier1_ok = true;
                                tier1_max_states = @max(tier1_max_states, states);
                            },
                            .falsified => |witness| {
                                falsified = true;
                                if (first_counterexample == null) first_counterexample = witness;
                                const msg = try std.fmt.allocPrint(self.alloc, "constitutional law '{s}' falsified at {s}", .{ lname, witness });
                                self.addError(.law_violation, cl_span, msg);
                            },
                            .inconclusive => {
                                const interval_violated = (is_never and (itruth == .always_true or itruth == .can_fail)) or
                                    (!is_never and (itruth == .always_false or itruth == .can_fail));
                                if (interval_violated) {
                                    violated = true;
                                    self.addError(.law_violation, cl_span, "constitutional law violated over possible input intervals");
                                } else {
                                    all_proved = false;
                                }
                            },
                        }
                    },
                }
            }

            if (!has_claim) all_proved = false;

            const verdict: LawVerdict = if (falsified)
                .falsified
            else if (violated)
                .violated
            else if (!all_proved)
                .unverified_symbolic
            else if (tier2_ok)
                .proved_tier2_symbolic
            else if (tier1_ok)
                .proved_tier1_exhaustive
            else if (interval_ok)
                .proved_interval
            else if (tier0_ok)
                .proved_tier0
            else
                .unverified_symbolic;

            const detail: []const u8 = switch (verdict) {
                .proved_tier0 => "Tier 0 (structural frame)",
                .proved_tier1_exhaustive => try std.fmt.allocPrint(self.alloc, "Tier 1 (exhaustive, {d} states)", .{tier1_max_states}),
                .proved_tier2_symbolic => "Tier 2 (symbolic auto-prover)",
                .proved_interval => "Tier 2 (interval bounds)",
                .proved_tier3_lean => "Tier 3 (Lean 4.35.0 kernel)",
                .falsified => if (first_counterexample) |ce|
                    try std.fmt.allocPrint(self.alloc, "FALSIFIED ({s})", .{ce})
                else
                    "FALSIFIED",
                .violated => "VIOLATED (Tier 0 / interval)",
                .unverified_symbolic => "UNPROVED",
            };

            try self.checked_laws.append(self.alloc, .{
                .name = lname,
                .span = decl.span,
                .verdict = verdict,
                .tier_detail = detail,
                .counterexample = first_counterexample,
                .symbolic_certs = try sym_certs.toOwnedSlice(self.alloc),
            });
        }
    }

    const IntervalTruth = enum {
        always_true,
        always_false,
        can_fail,
        unknown,
    };

    fn evalIntervalPredicate(self: *Analyzer, expr: *const ast.Expr, has_symbolic_guard: bool) std.mem.Allocator.Error!IntervalTruth {
        if (expr.* != .binary) return .unknown;
        const b = expr.binary;
        const lres = try self.checkExpr(b.left, null);
        const rres = try self.checkExpr(b.right, null);
        const lr = lres.range orelse lres.ty.rangeOf() orelse return .unknown;
        const rr = rres.range orelse rres.ty.rangeOf() orelse return .unknown;
        if (lr != .bounded or rr != .bounded) return .unknown;

        const lb = lr.bounded;
        const rb = rr.bounded;
        const one_side_const = (lb.lo == lb.hi) or (rb.lo == rb.hi);
        const raw: IntervalTruth = switch (b.op) {
            .le => if (lb.hi <= rb.lo) .always_true else if (lb.lo > rb.hi) .always_false else .can_fail,
            .lt => if (lb.hi < rb.lo) .always_true else if (lb.lo >= rb.hi) .always_false else .can_fail,
            .ge => if (lb.lo >= rb.hi) .always_true else if (lb.hi < rb.lo) .always_false else .can_fail,
            .gt => if (lb.lo > rb.hi) .always_true else if (lb.hi <= rb.lo) .always_false else .can_fail,
            .eq => if (lb.lo == lb.hi and rb.lo == rb.hi and lb.lo == rb.lo) .always_true else if (lb.hi < rb.lo or rb.hi < lb.lo) .always_false else .unknown,
            else => .unknown,
        };
        if (raw == .can_fail and (has_symbolic_guard or !one_side_const)) {
            return .unknown;
        }
        return raw;
    }
};

/// Run full semantic analysis (type/interval/borrow/layout/FFI/law verification)
/// on a parsed `ast.Ast`.
pub fn analyze(allocator: std.mem.Allocator, tree: *const ast.Ast) std.mem.Allocator.Error!CheckedModule {
    var arena = std.heap.ArenaAllocator.init(allocator);
    errdefer arena.deinit();
    const alloc = arena.allocator();

    var diagnostics: std.ArrayList(SemaDiagnostic) = .empty;
    var az = Analyzer{
        .alloc = alloc,
        .source = tree.source,
        .module = &tree.module,
        .diagnostics = &diagnostics,
        .record_defs = .empty,
        .adt_defs = .empty,
        .opaque_names = .empty,
        .type_aliases = .empty,
        .fn_sigs = .empty,
        .const_map = .empty,
        .scopes = .empty,
        .scope_marks = .empty,
        .active_views = .empty,
        .view_marks = .empty,
        .order_facts = .empty,
        .order_fact_marks = .empty,
        .current_accesses = null,
        .current_perm_trace = null,
        .current_disjoint_certs = null,
        .checked_collections = .empty,
        .checked_functions = .empty,
        .checked_laws = .empty,
        .expr_types = .empty,
        .let_types = .empty,
        .const_types = .empty,
        .current_fn_ret = null,
    };

    try az.registerTypeNames();
    try az.resolveAllTypeSignatures();
    try az.computeTransitiveCallEffects();
    try az.checkConstsAndFunctions();
    const records = try az.synthesizeAllLayouts();
    try az.checkLaws(records);

    const adts = try alloc.alloc(CheckedADT, az.adt_defs.items.len);
    for (az.adt_defs.items, 0..) |a, ai| {
        const vnames = try alloc.alloc([]const u8, a.variants.len);
        const variants = try alloc.alloc(CheckedADTVariant, a.variants.len);
        for (a.variants, 0..) |v, vi| {
            vnames[vi] = v.name;
            variants[vi] = .{
                .name = v.name,
                .field_types = v.field_types,
                .field_labels = v.field_labels,
            };
        }
        adts[ai] = .{
            .name = a.name,
            .span = a.span,
            .variant_names = vnames,
            .variants = variants,
            .adt_layout = layout.planCompactADT(a.variants.len, a.max_payload_bits),
        };
    }

    return .{
        .arena = arena,
        .source = tree.source,
        .records = records,
        .adts = adts,
        .collections = try az.checked_collections.toOwnedSlice(alloc),
        .functions = try az.checked_functions.toOwnedSlice(alloc),
        .laws = try az.checked_laws.toOwnedSlice(alloc),
        .diagnostics = try diagnostics.toOwnedSlice(alloc),
        .expr_types = az.expr_types,
        .let_types = az.let_types,
        .const_types = az.const_types,
        .call_type_args = az.call_type_args,
    };
}
