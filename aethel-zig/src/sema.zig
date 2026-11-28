const std = @import("std");
const lexer = @import("lexer.zig");
const ast = @import("ast.zig");
const int_range = @import("int_range.zig");
const layout = @import("layout.zig");
const law_verifier = @import("law_verifier.zig");

pub const IntType = int_range.IntType;
pub const IntRange = int_range.IntRange;

pub const ModuleSliceInfo = struct {
    module_id: usize,
    module_key: []const u8,
    start: usize,
    end: usize,
};

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
        non_exhaustive_match,
        visibility_error,
    };
};

pub const FnTy = struct {
    params: []const *const Ty,
    ret: *const Ty,
    is_once: bool = false,
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
    applied: struct {
        kind: AppliedKind,
        decl_idx: usize,
        args: []const *const Ty,
        brand_inst: ?[]const u8 = null,

        pub const AppliedKind = enum { record, adt, opaque_ty };
    },
    hkt_app: struct {
        ctor: []const u8,
        arg: *const Ty,
    },
    collection: struct {
        elem_record: ?usize,
        elem_ty: *const Ty,
    },
    vec: struct {
        elem_record: ?usize,
        elem_ty: *const Ty,
    },
    map: struct {
        key_ty: *const Ty,
        val_ty: *const Ty,
    },
    set: struct {
        elem_ty: *const Ty,
    },
    deque: struct {
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
    fn_ty: FnTy,
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
            .opaque_ty, .collection, .vec, .map, .set, .deque, .view, .path_borrow, .slice => false,
            .record, .adt => true,
            .applied => |ap| blk: {
                if (ap.kind == .opaque_ty) break :blk false;
                for (ap.args) |el| {
                    if (!el.isCopyable()) break :blk false;
                }
                break :blk true;
            },
            .hkt_app => true,
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
            .applied => |aa| blk: {
                const ab = b.applied;
                if (aa.kind != ab.kind or aa.decl_idx != ab.decl_idx or aa.args.len != ab.args.len) break :blk false;
                if (aa.brand_inst != null and ab.brand_inst != null and !std.mem.eql(u8, aa.brand_inst.?, ab.brand_inst.?)) {
                    break :blk false;
                }
                for (aa.args, ab.args) |ea, eb| {
                    if (!ea.eql(eb.*)) break :blk false;
                }
                break :blk true;
            },
            .hkt_app => |ha| std.mem.eql(u8, ha.ctor, b.hkt_app.ctor) and ha.arg.eql(b.hkt_app.arg.*),
            .type_var => |n| std.mem.eql(u8, n, b.type_var),
            .option => |inner| inner.eql(b.option.*),
            .slice => |sa| sa.mutable == b.slice.mutable and sa.elem.eql(b.slice.elem.*),
            .collection => |ca| ca.elem_ty.eql(b.collection.elem_ty.*),
            .vec => |va| va.elem_ty.eql(b.vec.elem_ty.*),
            .map => |ma| ma.key_ty.eql(b.map.key_ty.*) and ma.val_ty.eql(b.map.val_ty.*),
            .set => |sa| sa.elem_ty.eql(b.set.elem_ty.*),
            .deque => |da| da.elem_ty.eql(b.deque.elem_ty.*),
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
    rust_attrs: []const []const u8 = &.{},
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
    is_flat_c: bool = false,
    rust_derives: []const []const u8 = &.{},
    rust_attrs: []const []const u8 = &.{},
    has_pod_derive: bool = false,
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
    hkt_params: []const []const u8 = &.{},
    constraint_count: usize = 0,
    param_types: []const *const Ty,
    ret_type: *const Ty,
    reads: []const FieldAccessEffect,
    writes: []const FieldAccessEffect,
    preserves: []const usize,
    target_record: ?usize,
    has_extern_abi: bool,
    rust_sym: ?[]const u8 = null,
    perm_trace: []const PermTraceOp,
    disjoint_certs: []const DisjointCertEmit,
    decreases_certs: []const law_verifier.DecreasesCertEmit = &.{},
    returned_origin: ?usize,
};

pub const CheckedTraitParam = struct {
    name: []const u8,
    arity: u8,
};

pub const ResolvedConstraint = struct {
    trait_idx: usize,
    args: []const *const Ty,
    hkt_arg_names: []const ?[]const u8,
};

pub const CheckedTraitMethod = struct {
    name: []const u8,
    params: []const *const Ty,
    ret: *const Ty,
};

pub const CheckedTraitLaw = struct {
    name: []const u8,
    span: ast.Span,
};

pub const CheckedTrait = struct {
    name: []const u8,
    local_name: []const u8,
    params: []const CheckedTraitParam,
    supers: []const ResolvedConstraint,
    methods: []const CheckedTraitMethod,
    laws: []const CheckedTraitLaw,
};

pub const CheckedInstanceMethod = struct {
    local_name: []const u8,
    params: []const *const Ty,
    ret: *const Ty,
    type_params: []const []const u8,
    hkt_params: []const []const u8 = &.{},
    ast_method: ?ast.InstanceMethod = null,
    synth: law_verifier.SynthMethodKind = .none,
    ext_sym: ?[]const u8 = null,
};

pub const CheckedInstance = struct {
    name: []const u8,
    local_name: []const u8,
    module_id: usize,
    is_pub: bool,
    is_default: bool,
    is_external_rust: bool,
    rust_target: ?[]const u8,
    rust_sym: ?[]const u8,
    trait_idx: usize,
    target_tys: []const *const Ty,
    target_hkt_names: []const ?[]const u8,
    type_params: []const []const u8,
    hkt_params: []const []const u8 = &.{},
    constraints: []const ResolvedConstraint,
    methods: []const CheckedInstanceMethod,
    span: ast.Span,
};

pub const ForeignContract = struct {
    aethel_name: []const u8,
    rust_target: ?[]const u8 = null,
    rust_sym: []const u8,
    trait_name: ?[]const u8 = null,
    span: ast.Span,
};

pub const ResolvedWitness = union(enum) {
    concrete: struct {
        inst_idx: usize,
        type_args: []const *const Ty,
        hkt_args: []const ?[]const u8,
        sub_witnesses: []const ResolvedWitness,
    },
    param: usize,
};

pub const CallTraitResolution = struct {
    kind: Kind,
    witnesses: []const ResolvedWitness,
    type_args: []const *const Ty,
    hkt_args: []const ?[]const u8 = &.{},

    pub const Kind = union(enum) {
        constrained_fn: []const u8,
        trait_method: struct {
            method_name: []const u8,
            witness: ResolvedWitness,
        },
    };
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

pub const CheckedLawClause = struct {
    kind: std.meta.Tag(ast.LawClause),
    span: ast.Span,
    verdict: ?LawVerdict,
    detail: []const u8,
    certificate: ?[]const u8 = null,
    counterexample: ?[]const u8 = null,

    fn init(cl: ast.LawClause) CheckedLawClause {
        const span = switch (cl) {
            inline else => |c| c.span,
        };
        return .{
            .kind = std.meta.activeTag(cl),
            .span = span,
            .verdict = if (cl == .when) null else .unverified_symbolic,
            .detail = if (cl == .when) "guard for subsequent clauses" else "no proof for this clause",
        };
    }
};

pub const CheckedLaw = struct {
    name: []const u8,
    span: ast.Span,
    verdict: LawVerdict,
    clauses: []const CheckedLawClause = &.{},
    tier_detail: []const u8 = "",
    counterexample: ?[]const u8 = null,
    symbolic_certs: []const law_verifier.SymbolicLawCert = &.{},
};

pub const StdIntrinsicKind = enum {
    vec_new,
    vec_with_capacity,
    vec_len,
    vec_capacity,
    vec_is_empty,
    vec_push,
    vec_pop,
    vec_get,
    vec_set,
    vec_swap_remove,
    vec_reserve,
    vec_clear,
    vec_as_slice,
    vec_as_mut_slice,
    vec_as_collection,
    map_new,
    map_with_capacity,
    map_len,
    map_is_empty,
    map_insert,
    map_put,
    map_get,
    map_contains,
    map_remove,
    map_clear,
    set_new,
    set_with_capacity,
    set_len,
    set_is_empty,
    set_insert,
    set_contains,
    set_remove,
    set_clear,
    deque_new,
    deque_with_capacity,
    deque_len,
    deque_is_empty,
    deque_push_back,
    deque_push_front,
    deque_pop_front,
    deque_pop_back,
    deque_get,
    deque_clear,
    str_len,
    str_is_empty,
    str_eq,
    str_concat,
    str_repeat,
    str_starts_with,
    str_ends_with,
    str_contains,
    str_byte_at,
    str_slice_bytes,
};

pub const StdIntrinsicCall = struct {
    kind: StdIntrinsicKind,
    container_ty: *const Ty,
    recv_is_ptr: bool = false,
};

pub const CheckedModule = struct {
    arena: std.heap.ArenaAllocator,
    source: [:0]const u8,
    records: []const CheckedRecord,
    adts: []const CheckedADT,
    collections: []const CheckedCollection,
    dyn_vecs: []const CheckedCollection = &.{},
    functions: []const CheckedFunction,
    laws: []const CheckedLaw,
    diagnostics: []const SemaDiagnostic,
    expr_types: std.AutoHashMapUnmanaged(*const ast.Expr, *const Ty),
    let_types: std.AutoHashMapUnmanaged(usize, *const Ty),
    const_types: std.StringHashMapUnmanaged(*const Ty),
    call_type_args: std.AutoHashMapUnmanaged(*const ast.Expr, []const *const Ty),
    decl_canonical_names: std.AutoHashMapUnmanaged(usize, []const u8) = .empty,
    resolved_fn_calls: std.AutoHashMapUnmanaged(*const ast.Expr, []const u8) = .empty,
    resolved_idents: std.AutoHashMapUnmanaged(*const ast.Expr, []const u8) = .empty,
    resolved_records: std.AutoHashMapUnmanaged(*const ast.Expr, usize) = .empty,
    alias_types: std.StringHashMapUnmanaged(*const Ty) = .empty,
    traits: []const CheckedTrait = &.{},
    instances: []const CheckedInstance = &.{},
    foreign_contracts: []const ForeignContract = &.{},
    type_decl_params: std.AutoHashMapUnmanaged(usize, []const []const u8) = .empty,
    call_trait_resolutions: std.AutoHashMapUnmanaged(*const ast.Expr, CallTraitResolution) = .empty,
    numeral_trait_resolutions: std.AutoHashMapUnmanaged(*const ast.Expr, ResolvedWitness) = .empty,
    assign_trait_resolutions: std.AutoHashMapUnmanaged(*const ast.Stmt, CallTraitResolution) = .empty,
    std_intrinsic_calls: std.AutoHashMapUnmanaged(*const ast.Expr, StdIntrinsicCall) = .empty,

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

    pub fn declCanonicalName(self: *const CheckedModule, decl_start: usize) ?[]const u8 {
        return self.decl_canonical_names.get(decl_start);
    }

    pub fn resolvedCallName(self: *const CheckedModule, callee: *const ast.Expr) ?[]const u8 {
        return self.resolved_fn_calls.get(callee);
    }

    pub fn resolvedIdentName(self: *const CheckedModule, expr: *const ast.Expr) ?[]const u8 {
        return self.resolved_idents.get(expr);
    }

    pub fn resolvedRecordIdx(self: *const CheckedModule, expr: *const ast.Expr) ?usize {
        return self.resolved_records.get(expr);
    }

    pub fn aliasType(self: *const CheckedModule, canonical_name: []const u8) ?*const Ty {
        return self.alias_types.get(canonical_name);
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

const ReturnField = union(enum) {
    pending,
    precise: ParamFieldEffect,
    whole,
};

const FnSig = struct {
    name: []const u8,
    local_name: []const u8,
    module_id: usize = 0,
    is_pub: bool = true,
    span: ast.Span,
    type_params: []const []const u8 = &.{},
    hkt_params: []const []const u8 = &.{},
    constraints: []const ResolvedConstraint = &.{},
    params: []const *const Ty,
    param_auths: []const ?[]const usize,
    ret: *const Ty,
    target_record: ?usize,
    is_extern: bool,
    has_body: bool = true,
    rust_target: ?[]const u8 = null,
    rust_sym: ?[]const u8 = null,
    decl_index: ?usize,
    param_reads: std.ArrayList(ParamFieldEffect) = .empty,
    param_writes: std.ArrayList(ParamFieldEffect) = .empty,
    call_links: std.ArrayList(CallLink) = .empty,
    returned_origin: ?usize = null,
    returned_field: ?ParamFieldEffect = null,
};

const TraitMethodDef = struct {
    name: []const u8,
    sig: ast.TraitMethodSig,
    param_names: []const []const u8,
    params: []const *const Ty,
    ret: *const Ty,
    type_params: []const []const u8,
};

const TraitLawDef = struct {
    law: ast.TraitLaw,
    owner_trait_idx: usize,
};

const TraitDef = struct {
    name: []const u8,
    local_name: []const u8,
    module_id: usize = 0,
    is_pub: bool = true,
    span: ast.Span,
    decl_ast: ast.Decl.Kind,
    params: []const CheckedTraitParam,
    supers: []const ResolvedConstraint,
    methods: []const TraitMethodDef,
    laws: []const ast.TraitLaw,
};

const InstanceDef = struct {
    name: []const u8,
    local_name: []const u8,
    module_id: usize = 0,
    is_pub: bool = true,
    is_default: bool = false,
    is_external_rust: bool = false,
    rust_target: ?[]const u8 = null,
    rust_sym: ?[]const u8 = null,
    span: ast.Span,
    decl_ast: ast.Decl.Kind,
    trait_idx: usize,
    target_tys: []const *const Ty,
    target_hkt_names: []const ?[]const u8,
    type_params: []const []const u8,
    hkt_params: []const []const u8,
    constraints: []const ResolvedConstraint,
    methods: []const CheckedInstanceMethod,
};

const ConstEntry = struct {
    name: []const u8,
    local_name: []const u8,
    module_id: usize = 0,
    is_pub: bool = true,
    ty: *const Ty,
    range: ?IntRange,
};

const OpaqueDef = struct {
    name: []const u8,
    local_name: []const u8,
    module_id: usize = 0,
    is_pub: bool = true,
};

const TypeAliasEntry = struct {
    name: []const u8,
    local_name: []const u8,
    module_id: usize = 0,
    is_pub: bool = true,
    ty: *const Ty,
};

const ModuleAliasImport = struct {
    importer_mod: usize,
    alias: []const u8,
    target_mod: usize,
};

const MemberImport = struct {
    importer_mod: usize,
    member_name: []const u8,
    target_mod: usize,
    span: ast.Span,
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
    opaque_defs: std.ArrayList(OpaqueDef),
    type_alias_entries: std.ArrayList(TypeAliasEntry),
    type_aliases: std.StringHashMapUnmanaged(*const Ty),
    fn_sigs: std.ArrayList(FnSig),
    const_map: std.StringHashMapUnmanaged(ConstEntry),
    const_list: std.ArrayList(ConstEntry) = .empty,
    module_slices: []const ModuleSliceInfo = &.{},
    entry_module_id: usize = 0,
    current_module_id: usize = 0,
    alias_imports: std.ArrayList(ModuleAliasImport) = .empty,
    member_imports: std.ArrayList(MemberImport) = .empty,
    decl_canonical_names: std.AutoHashMapUnmanaged(usize, []const u8) = .empty,
    resolved_fn_calls: std.AutoHashMapUnmanaged(*const ast.Expr, []const u8) = .empty,
    resolved_idents: std.AutoHashMapUnmanaged(*const ast.Expr, []const u8) = .empty,
    resolved_records: std.AutoHashMapUnmanaged(*const ast.Expr, usize) = .empty,

    scopes: std.ArrayList(Binding),
    field_ranges: std.ArrayListUnmanaged(FieldRangeEntry) = .empty,
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
    checked_dyn_vecs: std.ArrayList(CheckedCollection) = .empty,
    checked_functions: std.ArrayList(CheckedFunction),
    checked_laws: std.ArrayList(CheckedLaw),

    expr_types: std.AutoHashMapUnmanaged(*const ast.Expr, *const Ty),
    let_types: std.AutoHashMapUnmanaged(usize, *const Ty),
    const_types: std.StringHashMapUnmanaged(*const Ty),
    call_type_args: std.AutoHashMapUnmanaged(*const ast.Expr, []const *const Ty) = .empty,
    std_intrinsic_calls: std.AutoHashMapUnmanaged(*const ast.Expr, StdIntrinsicCall) = .empty,
    trait_defs: std.ArrayList(TraitDef) = .empty,
    instance_defs: std.ArrayList(InstanceDef) = .empty,
    foreign_contracts: std.ArrayList(ForeignContract) = .empty,
    type_decl_params: std.AutoHashMapUnmanaged(usize, []const []const u8) = .empty,
    call_trait_resolutions: std.AutoHashMapUnmanaged(*const ast.Expr, CallTraitResolution) = .empty,
    numeral_trait_resolutions: std.AutoHashMapUnmanaged(*const ast.Expr, ResolvedWitness) = .empty,
    assign_trait_resolutions: std.AutoHashMapUnmanaged(*const ast.Stmt, CallTraitResolution) = .empty,
    active_hkt_params: std.ArrayList([]const u8) = .empty,
    active_constraints: []const ResolvedConstraint = &.{},
    active_using_stack: std.ArrayList([]const usize) = .empty,
    current_fn_ret: ?*const Ty,
    inferred_return_origin: ?usize = null,
    inferred_return_field: ReturnField = .pending,
    current_decreases_certs: ?*std.ArrayList(law_verifier.DecreasesCertEmit) = null,
    current_fn_name: ?[]const u8 = null,
    current_fn_params: []const []const u8 = &.{},
    project_pkg_name: ?[]const u8 = null,
    declared_rust_crates: ?[]const []const u8 = null,
    current_fn_decreases: ?*const ast.Expr = null,
    current_sym_guards: std.ArrayList(*const ast.Expr) = .empty,

    const FieldRangeEntry = struct {
        root: []const u8,
        field: []const u8,
        range: IntRange,
    };

    const RecordDef = struct {
        name: []const u8,
        local_name: []const u8,
        module_id: usize = 0,
        is_pub: bool = true,
        span: ast.Span,
        fields: []CheckedField,
        conflicts: std.ArrayList(layout.ConflictPair),
        collection_layout: ?layout.CollectionLayout,
        decl_ast: ast.Decl.Kind,
        auto_layout_requested: bool = false,
        simd_loop_seen: bool = false,
        hot_fields: []bool = &.{},
        address_taken_fields: []bool = &.{},
        observed_collection_len: ?usize = null,
        is_flat_c: bool = false,
        is_packed_attr: bool = false,
        rust_derives: []const []const u8 = &.{},
        rust_attrs: []const []const u8 = &.{},
        has_pod_derive: bool = false,
        fields_resolved: bool = false,
        used_in_dyn_vec: bool = false,
        type_params: []const []const u8 = &.{},
        constraints: []const ResolvedConstraint = &.{},
    };

    const ADTDef = struct {
        name: []const u8,
        local_name: []const u8,
        module_id: usize = 0,
        is_pub: bool = true,
        span: ast.Span,
        variants: []VariantInfo,
        max_payload_bits: u16,
        type_params: []const []const u8 = &.{},
        constraints: []const ResolvedConstraint = &.{},
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

    fn moduleIdOfSpan(self: *const Analyzer, span: ast.Span) usize {
        if (self.module_slices.len == 0) return 0;
        for (self.module_slices) |sl| {
            if (span.start >= sl.start and span.start < sl.end) return sl.module_id;
        }
        return self.entry_module_id;
    }

    fn canonicalName(self: *Analyzer, mod_id: usize, local_name: []const u8, no_mangle: bool) std.mem.Allocator.Error![]const u8 {
        if (no_mangle or self.module_slices.len <= 1 or mod_id == self.entry_module_id) {
            return local_name;
        }
        var mkey: []const u8 = "";
        for (self.module_slices) |sl| {
            if (sl.module_id == mod_id) {
                mkey = sl.module_key;
                break;
            }
        }
        if (mkey.len == 0) return local_name;
        var buf: std.ArrayList(u8) = .empty;
        try buf.appendSlice(self.alloc, "mod__");
        for (mkey) |ch| {
            if ((ch >= 'a' and ch <= 'z') or (ch >= 'A' and ch <= 'Z') or (ch >= '0' and ch <= '9')) {
                try buf.append(self.alloc, ch);
            } else {
                try buf.append(self.alloc, '_');
            }
        }
        try buf.appendSlice(self.alloc, "__");
        try buf.appendSlice(self.alloc, local_name);
        return try buf.toOwnedSlice(self.alloc);
    }

    fn resolveImportedModule(self: *const Analyzer, from_mod: usize, qualifier: []const u8) ?usize {
        for (self.alias_imports.items) |ai| {
            if (ai.importer_mod == from_mod and std.mem.eql(u8, ai.alias, qualifier)) {
                return ai.target_mod;
            }
        }
        return null;
    }

    fn memberImportTarget(self: *const Analyzer, from_mod: usize, member: []const u8) ?usize {
        for (self.member_imports.items) |mi| {
            if (mi.importer_mod == from_mod and std.mem.eql(u8, mi.member_name, member)) {
                return mi.target_mod;
            }
        }
        return null;
    }

    fn registerImports(self: *Analyzer) std.mem.Allocator.Error!void {
        if (self.module_slices.len == 0) return;
        for (self.module.decls) |decl| {
            if (decl.kind != .import_decl) continue;
            const imp = decl.kind.import_decl;
            if (imp.path.len == 0) continue;
            const from_mod = self.moduleIdOfSpan(decl.span);

            var key_buf: std.ArrayList(u8) = .empty;
            for (imp.path, 0..) |seg, i| {
                if (i > 0) try key_buf.append(self.alloc, '/');
                try key_buf.appendSlice(self.alloc, seg.slice(self.source));
            }
            const imp_key = try key_buf.toOwnedSlice(self.alloc);

            var target_mod_opt: ?usize = null;
            for (self.module_slices) |sl| {
                if (std.mem.eql(u8, sl.module_key, imp_key)) {
                    target_mod_opt = sl.module_id;
                    break;
                }
            }
            if (target_mod_opt == null) {
                // Relative lookup inside subdirectory if importing sibling file.
                var from_key: []const u8 = "";
                for (self.module_slices) |sl| {
                    if (sl.module_id == from_mod) {
                        from_key = sl.module_key;
                        break;
                    }
                }
                if (std.fs.path.dirname(from_key)) |fdir| {
                    const rel_key = try std.fmt.allocPrint(self.alloc, "{s}/{s}", .{ fdir, imp_key });
                    for (self.module_slices) |sl| {
                        if (std.mem.eql(u8, sl.module_key, rel_key)) {
                            target_mod_opt = sl.module_id;
                            break;
                        }
                    }
                }
            }
            const target_mod = target_mod_opt orelse continue;
            const alias_name = if (imp.alias) |a|
                a.slice(self.source)
            else
                imp.path[imp.path.len - 1].slice(self.source);
            try self.alias_imports.append(self.alloc, .{
                .importer_mod = from_mod,
                .alias = alias_name,
                .target_mod = target_mod,
            });
            for (imp.members) |m| {
                try self.member_imports.append(self.alloc, .{
                    .importer_mod = from_mod,
                    .member_name = m.slice(self.source),
                    .target_mod = target_mod,
                    .span = m,
                });
            }
        }
    }

    fn findRecordIndex(self: *const Analyzer, name: []const u8) ?usize {
        for (self.record_defs.items, 0..) |r, idx| {
            if (std.mem.eql(u8, r.name, name)) return idx;
        }
        return null;
    }

    fn findRecordInModule(self: *const Analyzer, mod_id: usize, local_name: []const u8) ?usize {
        for (self.record_defs.items, 0..) |r, idx| {
            if (r.module_id == mod_id and std.mem.eql(u8, r.local_name, local_name)) return idx;
        }
        return null;
    }

    fn findADTIndex(self: *const Analyzer, name: []const u8) ?usize {
        for (self.adt_defs.items, 0..) |a, idx| {
            if (std.mem.eql(u8, a.name, name)) return idx;
        }
        return null;
    }

    fn findADTInModule(self: *const Analyzer, mod_id: usize, local_name: []const u8) ?usize {
        for (self.adt_defs.items, 0..) |a, idx| {
            if (a.module_id == mod_id and std.mem.eql(u8, a.local_name, local_name)) return idx;
        }
        return null;
    }

    fn findOpaqueIndex(self: *const Analyzer, name: []const u8) ?usize {
        for (self.opaque_defs.items, 0..) |n, idx| {
            if (std.mem.eql(u8, n.name, name)) return idx;
        }
        return null;
    }

    fn findTraitInModule(self: *const Analyzer, mod_id: usize, local_name: []const u8) ?usize {
        for (self.trait_defs.items, 0..) |t, idx| {
            if (t.module_id == mod_id and std.mem.eql(u8, t.local_name, local_name)) return idx;
        }
        return null;
    }

    fn findTraitIndex(self: *const Analyzer, name: []const u8) ?usize {
        for (self.trait_defs.items, 0..) |t, idx| {
            if (std.mem.eql(u8, t.name, name) or std.mem.eql(u8, t.local_name, name)) return idx;
        }
        return null;
    }

    fn findInstanceIndex(self: *const Analyzer, name: []const u8) ?usize {
        for (self.instance_defs.items, 0..) |inst, idx| {
            if (std.mem.eql(u8, inst.name, name) or std.mem.eql(u8, inst.local_name, name)) return idx;
        }
        return null;
    }

    fn resolveVisibleTraitIndex(self: *Analyzer, name: []const u8, err_span: ast.Span) ?usize {
        if (self.findTraitInModule(self.current_module_id, name)) |ti| return ti;
        if (self.memberImportTarget(self.current_module_id, name)) |target_mod| {
            if (self.findTraitInModule(target_mod, name)) |ti| {
                if (!self.trait_defs.items[ti].is_pub and target_mod != self.current_module_id) {
                    self.addError(.visibility_error, err_span, "cannot access private trait from imported module");
                }
                return ti;
            }
        }
        if (self.findTraitIndex(name)) |ti| {
            if (self.module_slices.len > 0 and self.trait_defs.items[ti].module_id != self.current_module_id and !self.trait_defs.items[ti].is_pub) {
                self.addError(.visibility_error, err_span, "cannot access private trait");
            }
            return ti;
        }
        return null;
    }

    fn findOpaqueInModule(self: *const Analyzer, mod_id: usize, local_name: []const u8) ?usize {
        for (self.opaque_defs.items, 0..) |o, idx| {
            if (o.module_id == mod_id and std.mem.eql(u8, o.local_name, local_name)) return idx;
        }
        return null;
    }

    fn findTypeAliasInModule(self: *const Analyzer, mod_id: usize, local_name: []const u8) ?*const TypeAliasEntry {
        for (self.type_alias_entries.items) |*ta| {
            if (ta.module_id == mod_id and std.mem.eql(u8, ta.local_name, local_name)) return ta;
        }
        return null;
    }

    fn findFnIndex(self: *const Analyzer, name: []const u8) ?usize {
        for (self.fn_sigs.items, 0..) |f, idx| {
            if (std.mem.eql(u8, f.name, name)) return idx;
        }
        return null;
    }

    fn findFnInModule(self: *const Analyzer, mod_id: usize, local_name: []const u8) ?usize {
        for (self.fn_sigs.items, 0..) |f, idx| {
            if (f.module_id == mod_id and std.mem.eql(u8, f.local_name, local_name)) return idx;
        }
        return null;
    }

    fn findConstInModule(self: *const Analyzer, mod_id: usize, local_name: []const u8) ?*const ConstEntry {
        for (self.const_list.items) |*c| {
            if (c.module_id == mod_id and std.mem.eql(u8, c.local_name, local_name)) return c;
        }
        return null;
    }

    fn resolveVisibleFnIndex(self: *Analyzer, local_name: []const u8, err_span: ?ast.Span) ?usize {
        if (self.findFnInModule(self.current_module_id, local_name)) |fidx| return fidx;
        if (self.memberImportTarget(self.current_module_id, local_name)) |target_mod| {
            if (self.findFnInModule(target_mod, local_name)) |fidx| {
                if (!self.fn_sigs.items[fidx].is_pub and target_mod != self.current_module_id) {
                    if (err_span) |sp| self.addError(.visibility_error, sp, "cannot access private function from imported module");
                }
                return fidx;
            }
        }
        if (self.module_slices.len == 0) return self.findFnIndex(local_name);
        return null;
    }

    fn resolveQualifiedFnIndex(self: *Analyzer, qualifier: []const u8, fn_name: []const u8, err_span: ?ast.Span) ?usize {
        const target_mod = self.resolveImportedModule(self.current_module_id, qualifier) orelse return null;
        const fidx = self.findFnInModule(target_mod, fn_name) orelse return null;
        if (!self.fn_sigs.items[fidx].is_pub and target_mod != self.current_module_id) {
            if (err_span) |sp| self.addError(.visibility_error, sp, "function is private in imported module");
        }
        return fidx;
    }

    fn resolveCalleeFnIndex(self: *Analyzer, callee: *const ast.Expr, report_visibility: bool) ?usize {
        if (callee.* == .ident) {
            return self.resolveVisibleFnIndex(callee.ident.slice(self.source), if (report_visibility) callee.ident else null);
        }
        if (callee.* == .field and callee.field.target.* == .ident) {
            const qual = callee.field.target.ident.slice(self.source);
            if (self.lookupVar(qual) == null) {
                return self.resolveQualifiedFnIndex(qual, callee.field.name.slice(self.source), if (report_visibility) callee.field.name else null);
            }
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
            const mod_id = self.moduleIdOfSpan(decl.span);
            switch (decl.kind) {
                .type_decl => |td| {
                    const local_name = td.name.slice(self.source);
                    if (self.findRecordInModule(mod_id, local_name) != null or
                        self.findADTInModule(mod_id, local_name) != null or
                        self.findOpaqueInModule(mod_id, local_name) != null or
                        self.findTypeAliasInModule(mod_id, local_name) != null)
                    {
                        self.addError(.duplicate_decl, td.name, "duplicate type declaration");
                        continue;
                    }
                    const cname = try self.canonicalName(mod_id, local_name, false);
                    try self.decl_canonical_names.put(self.alloc, decl.span.start, cname);
                    switch (td.body) {
                        .empty => {
                            try self.opaque_defs.append(self.alloc, .{
                                .name = cname,
                                .local_name = local_name,
                                .module_id = mod_id,
                                .is_pub = decl.is_pub,
                            });
                        },
                        .alias => {
                            const err_ty = try self.allocTy(.err);
                            try self.type_aliases.put(self.alloc, cname, err_ty);
                            try self.type_alias_entries.append(self.alloc, .{
                                .name = cname,
                                .local_name = local_name,
                                .module_id = mod_id,
                                .is_pub = decl.is_pub,
                                .ty = err_ty,
                            });
                        },
                        .record => |fields| {
                            var col_lay: ?layout.CollectionLayout = null;
                            var auto_req = false;
                            var is_flat = false;
                            var is_packed = false;
                            for (decl.attrs) |attr| {
                                if (attr.payload == .layout) {
                                    switch (attr.payload.layout) {
                                        .auto => auto_req = true,
                                        .flat => is_flat = true,
                                        .@"packed" => is_packed = true,
                                        else => col_lay = try self.resolveLayoutAttr(attr.span, attr.payload.layout),
                                    }
                                }
                            }
                            const rec_rust = try self.parseRustRecordAttrs(decl.attrs, is_flat);
                            var tps = try self.alloc.alloc([]const u8, td.type_params.len);
                            for (td.type_params, 0..) |tp, ti| tps[ti] = tp.slice(self.source);
                            if (tps.len > 0) try self.type_decl_params.put(self.alloc, self.record_defs.items.len, tps);
                            const fslice = try self.alloc.alloc(CheckedField, fields.len);
                            const hslice = try self.alloc.alloc(bool, fields.len);
                            @memset(hslice, false);
                            const aslice = try self.alloc.alloc(bool, fields.len);
                            @memset(aslice, false);
                            try self.record_defs.append(self.alloc, .{
                                .name = cname,
                                .local_name = local_name,
                                .module_id = mod_id,
                                .is_pub = decl.is_pub,
                                .span = decl.span,
                                .fields = fslice,
                                .conflicts = .empty,
                                .collection_layout = col_lay,
                                .decl_ast = decl.kind,
                                .auto_layout_requested = auto_req,
                                .hot_fields = hslice,
                                .address_taken_fields = aslice,
                                .is_flat_c = is_flat,
                                .is_packed_attr = is_packed,
                                .rust_derives = rec_rust.derives,
                                .rust_attrs = rec_rust.attrs,
                                .has_pod_derive = rec_rust.has_pod_derive,
                                .type_params = tps,
                            });
                        },
                        .variants => |variants| {
                            var tps = try self.alloc.alloc([]const u8, td.type_params.len);
                            for (td.type_params, 0..) |tp, ti| tps[ti] = tp.slice(self.source);
                            const vslice = try self.alloc.alloc(VariantInfo, variants.len);
                            try self.adt_defs.append(self.alloc, .{
                                .name = cname,
                                .local_name = local_name,
                                .module_id = mod_id,
                                .is_pub = decl.is_pub,
                                .span = decl.span,
                                .variants = vslice,
                                .max_payload_bits = 0,
                                .type_params = tps,
                            });
                        },
                    }
                },
                .trait_decl => |tr| {
                    const local_name = tr.name.slice(self.source);
                    if (self.findTraitInModule(mod_id, local_name) != null) {
                        self.addError(.duplicate_decl, tr.name, "duplicate trait declaration");
                        continue;
                    }
                    const cname = try self.canonicalName(mod_id, local_name, false);
                    try self.decl_canonical_names.put(self.alloc, decl.span.start, cname);
                    var tparams = try self.alloc.alloc(CheckedTraitParam, tr.params.len);
                    for (tr.params, 0..) |tp, ti| {
                        tparams[ti] = .{ .name = tp.name.slice(self.source), .arity = tp.arity };
                    }
                    try self.trait_defs.append(self.alloc, .{
                        .name = cname,
                        .local_name = local_name,
                        .module_id = mod_id,
                        .is_pub = decl.is_pub,
                        .span = decl.span,
                        .decl_ast = decl.kind,
                        .params = tparams,
                        .supers = &.{},
                        .methods = &.{},
                        .laws = tr.laws,
                    });
                },
                else => {},
            }
        }
    }

    fn resolveLayoutAttr(self: *Analyzer, span: ast.Span, spec: ast.LayoutSpec) std.mem.Allocator.Error!?layout.CollectionLayout {
        return switch (spec) {
            .aos => .aos,
            .soa => .soa,
            .auto, .@"packed", .flat => null,
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
            .vec => |v| try self.collectTypeVars(v.elem_ty, list),
            .map => |m| {
                try self.collectTypeVars(m.key_ty, list);
                try self.collectTypeVars(m.val_ty, list);
            },
            .set => |s| try self.collectTypeVars(s.elem_ty, list),
            .deque => |d| try self.collectTypeVars(d.elem_ty, list),
            .view => |v| try self.collectTypeVars(v.target, list),
            .path_borrow => |pb| try self.collectTypeVars(pb.base, list),
            .tuple => |elems| for (elems) |el| try self.collectTypeVars(el, list),
            .fn_ty => |ft| {
                for (ft.params) |pt| try self.collectTypeVars(pt, list);
                try self.collectTypeVars(ft.ret, list);
            },
            .applied => |ap| {
                for (ap.args) |el| try self.collectTypeVars(el, list);
            },
            .hkt_app => |ha| {
                try self.collectTypeVars(ha.arg, list);
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
            .vec => |v| containsUnresolvedTypeVar(v.elem_ty, subst),
            .map => |m| containsUnresolvedTypeVar(m.key_ty, subst) or containsUnresolvedTypeVar(m.val_ty, subst),
            .set => |s| containsUnresolvedTypeVar(s.elem_ty, subst),
            .deque => |d| containsUnresolvedTypeVar(d.elem_ty, subst),
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
            .applied => |ap| blk: {
                for (ap.args) |el| if (containsUnresolvedTypeVar(el, subst)) break :blk true;
                break :blk false;
            },
            .hkt_app => |ha| containsUnresolvedTypeVar(ha.arg, subst),
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
                if (actual.* == .collection) {
                    return try self.unifyType(fc.elem_ty, actual.collection.elem_ty, subst);
                }
                if (actual.* == .vec) {
                    return try self.unifyType(fc.elem_ty, actual.vec.elem_ty, subst);
                }
                return false;
            },
            .vec => |fv| {
                if (actual.* != .vec) return false;
                return try self.unifyType(fv.elem_ty, actual.vec.elem_ty, subst);
            },
            .map => |fm| {
                if (actual.* != .map) return false;
                return (try self.unifyType(fm.key_ty, actual.map.key_ty, subst)) and
                    (try self.unifyType(fm.val_ty, actual.map.val_ty, subst));
            },
            .set => |fs| {
                if (actual.* != .set) return false;
                return try self.unifyType(fs.elem_ty, actual.set.elem_ty, subst);
            },
            .deque => |fd| {
                if (actual.* != .deque) return false;
                return try self.unifyType(fd.elem_ty, actual.deque.elem_ty, subst);
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
            .applied => |fa| {
                if (actual.* != .applied or fa.kind != actual.applied.kind or fa.decl_idx != actual.applied.decl_idx or fa.args.len != actual.applied.args.len) return false;
                for (fa.args, actual.applied.args) |fe, ae| {
                    if (!try self.unifyType(fe, ae, subst)) return false;
                }
                return true;
            },
            .hkt_app => |fha| {
                const hkt_key = try std.fmt.allocPrint(self.alloc, "__hkt__{s}", .{fha.ctor});
                switch (actual.*) {
                    .option => |ai| {
                        if (subst.get(hkt_key)) |prev| {
                            if (prev.* != .option) return false;
                        } else {
                            try subst.put(self.alloc, hkt_key, try self.allocTy(.{ .option = try self.allocTy(.err) }));
                        }
                        if (ai.* == .err) return true;
                        return try self.unifyType(fha.arg, ai, subst);
                    },
                    .applied => |ap| {
                        if (ap.args.len != 1) return false;
                        if (subst.get(hkt_key)) |prev| {
                            if (prev.* != .applied or prev.applied.kind != ap.kind or prev.applied.decl_idx != ap.decl_idx) return false;
                        } else {
                            try subst.put(self.alloc, hkt_key, try self.allocTy(.{ .applied = .{
                                .kind = ap.kind,
                                .decl_idx = ap.decl_idx,
                                .args = &.{},
                                .brand_inst = ap.brand_inst,
                            } }));
                        }
                        return try self.unifyType(fha.arg, ap.args[0], subst);
                    },
                    .hkt_app => |aha| {
                        if (subst.get(hkt_key)) |prev| {
                            if (prev.* != .hkt_app or !std.mem.eql(u8, prev.hkt_app.ctor, aha.ctor)) return false;
                        } else {
                            try subst.put(self.alloc, hkt_key, try self.allocTy(.{ .hkt_app = .{
                                .ctor = aha.ctor,
                                .arg = try self.allocTy(.err),
                            } }));
                        }
                        return try self.unifyType(fha.arg, aha.arg, subst);
                    },
                    else => return false,
                }
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
            .vec => |v| {
                const sub = try self.substituteType(v.elem_ty, subst);
                return if (sub == v.elem_ty) ty else try self.allocTy(.{ .vec = .{
                    .elem_record = recordOfType(sub),
                    .elem_ty = sub,
                } });
            },
            .map => |m| {
                const sk = try self.substituteType(m.key_ty, subst);
                const sv = try self.substituteType(m.val_ty, subst);
                return if (sk == m.key_ty and sv == m.val_ty) ty else try self.allocTy(.{ .map = .{
                    .key_ty = sk,
                    .val_ty = sv,
                } });
            },
            .set => |s| {
                const sub = try self.substituteType(s.elem_ty, subst);
                return if (sub == s.elem_ty) ty else try self.allocTy(.{ .set = .{ .elem_ty = sub } });
            },
            .deque => |d| {
                const sub = try self.substituteType(d.elem_ty, subst);
                return if (sub == d.elem_ty) ty else try self.allocTy(.{ .deque = .{ .elem_ty = sub } });
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
            .applied => |ap| {
                const out = try self.alloc.alloc(*const Ty, ap.args.len);
                var changed = false;
                for (ap.args, 0..) |el, i| {
                    out[i] = try self.substituteType(el, subst);
                    if (out[i] != el) changed = true;
                }
                return if (!changed) ty else try self.allocTy(.{ .applied = .{
                    .kind = ap.kind,
                    .decl_idx = ap.decl_idx,
                    .args = out,
                    .brand_inst = ap.brand_inst,
                } });
            },
            .hkt_app => |ha| {
                const sarg = try self.substituteType(ha.arg, subst);
                const hkt_key = std.fmt.allocPrint(self.alloc, "__hkt__{s}", .{ha.ctor}) catch return ty;
                if (subst.get(hkt_key)) |ctor_ty| {
                    switch (ctor_ty.*) {
                        .option => return try self.allocTy(.{ .option = sarg }),
                        .applied => |ap| return try self.allocTy(.{ .applied = .{
                            .kind = ap.kind,
                            .decl_idx = ap.decl_idx,
                            .args = try self.alloc.dupe(*const Ty, &.{sarg}),
                            .brand_inst = ap.brand_inst,
                        } }),
                        .hkt_app => |nha| return try self.allocTy(.{ .hkt_app = .{ .ctor = nha.ctor, .arg = sarg } }),
                        else => {},
                    }
                }
                return if (sarg == ha.arg) ty else try self.allocTy(.{ .hkt_app = .{ .ctor = ha.ctor, .arg = sarg } });
            },
            else => return ty,
        }
    }

    const ExternalRustSpec = struct {
        target: ?[]const u8 = null,
        sym: []const u8,
        span: ast.Span,
    };

    fn stripStringQuotes(s: []const u8) []const u8 {
        if (s.len >= 2 and s[0] == '"' and s[s.len - 1] == '"') {
            return s[1 .. s.len - 1];
        }
        return s;
    }

    fn parseExternalRustAttr(self: *Analyzer, attrs: []const ast.Attribute, fallback_name: []const u8) ?ExternalRustSpec {
        for (attrs) |attr| {
            const aname = attr.name.slice(self.source);
            if (!std.mem.eql(u8, aname, "external")) continue;
            if (attr.payload != .args or attr.payload.args.len == 0) {
                self.addError(.invalid_ffi_type, attr.span, "@external requires target language, e.g. @external(rust, \"symbol\")");
                return null;
            }
            const lang_expr = attr.payload.args[0];
            const lang = switch (lang_expr.*) {
                .ident => |sp| sp.slice(self.source),
                .string_lit => |sp| stripStringQuotes(sp.slice(self.source)),
                else => "",
            };
            if (!std.mem.eql(u8, lang, "rust")) {
                self.addError(.invalid_ffi_type, attr.span, "unsupported @external target (strictly Rust -> Aethel interop via @external(rust, ...))");
                return null;
            }
            if (attr.payload.args.len == 1) {
                return .{ .target = null, .sym = fallback_name, .span = attr.span };
            }
            if (attr.payload.args.len == 2) {
                const sym = switch (attr.payload.args[1].*) {
                    .string_lit => |sp| stripStringQuotes(sp.slice(self.source)),
                    .ident => |sp| sp.slice(self.source),
                    else => fallback_name,
                };
                return .{ .target = null, .sym = sym, .span = attr.span };
            }
            const tgt = switch (attr.payload.args[1].*) {
                .string_lit => |sp| stripStringQuotes(sp.slice(self.source)),
                .ident, .upper_ident => |sp| sp.slice(self.source),
                else => "",
            };
            const sym = switch (attr.payload.args[2].*) {
                .string_lit => |sp| stripStringQuotes(sp.slice(self.source)),
                .ident => |sp| sp.slice(self.source),
                else => fallback_name,
            };
            return .{ .target = tgt, .sym = sym, .span = attr.span };
        }
        return null;
    }

    fn resolveTypeWithHKT(self: *Analyzer, ty_ast: *const ast.TypeExpr) std.mem.Allocator.Error!*const Ty {
        return try self.resolveType(ty_ast);
    }

    fn hktArgNameFromTypeExpr(self: *Analyzer, ty_ast: *const ast.TypeExpr) ?[]const u8 {
        return switch (ty_ast.*) {
            .named => |n| if (n.path.len > 0) blk: {
                const head = n.path[n.path.len - 1].slice(self.source);
                if (std.mem.eql(u8, head, "Option")) break :blk "Option";
                if (self.findRecordInModule(self.current_module_id, head)) |ri| break :blk self.record_defs.items[ri].name;
                if (self.findADTInModule(self.current_module_id, head)) |ai| break :blk self.adt_defs.items[ai].name;
                if (self.findRecordIndex(head)) |ri| break :blk self.record_defs.items[ri].name;
                if (self.findADTIndex(head)) |ai| break :blk self.adt_defs.items[ai].name;
                break :blk head;
            } else null,
            .type_var => |tv| tv.name.slice(self.source),
            else => null,
        };
    }

    fn resolveTraitConstraint(self: *Analyzer, tc: ast.TraitConstraint) std.mem.Allocator.Error!?ResolvedConstraint {
        if (tc.path.len == 0) return null;
        const tname = tc.path[tc.path.len - 1].slice(self.source);
        const ti = self.resolveVisibleTraitIndex(tname, tc.span) orelse {
            self.addError(.unknown_type, tc.span, "unknown trait in constraint");
            return null;
        };
        const tr = self.trait_defs.items[ti];
        const args = try self.alloc.alloc(*const Ty, tc.args.len);
        const hkts = try self.alloc.alloc(?[]const u8, tc.args.len);
        for (tc.args, 0..) |a, ai| {
            const is_hkt = ai < tr.params.len and tr.params[ai].arity >= 1;
            if (is_hkt) {
                const hname = self.hktArgNameFromTypeExpr(a);
                hkts[ai] = hname;
                args[ai] = try self.allocTy(.{ .type_var = hname orelse "_" });
            } else {
                hkts[ai] = null;
                args[ai] = try self.resolveType(a);
            }
        }
        return .{ .trait_idx = ti, .args = args, .hkt_arg_names = hkts };
    }

    fn traitHasSuper(self: *const Analyzer, sub_idx: usize, target_idx: usize) bool {
        if (sub_idx == target_idx) return true;
        if (sub_idx >= self.trait_defs.items.len) return false;
        for (self.trait_defs.items[sub_idx].supers) |sup| {
            if (self.traitHasSuper(sup.trait_idx, target_idx)) return true;
        }
        return false;
    }

    const RequiredTraitMethod = struct {
        owner_trait_idx: usize,
        def: TraitMethodDef,
    };

    fn collectTraitAndSuperMethods(
        self: *const Analyzer,
        trait_idx: usize,
        out: *std.ArrayList(RequiredTraitMethod),
    ) std.mem.Allocator.Error!void {
        if (trait_idx >= self.trait_defs.items.len) return;
        const tr = self.trait_defs.items[trait_idx];
        for (tr.supers) |sup| {
            try self.collectTraitAndSuperMethods(sup.trait_idx, out);
        }
        for (tr.methods) |m| {
            var exists = false;
            for (out.items) |prev| {
                if (std.mem.eql(u8, prev.def.name, m.name)) {
                    exists = true;
                    break;
                }
            }
            if (!exists) try out.append(self.alloc, .{ .owner_trait_idx = trait_idx, .def = m });
        }
    }

    fn collectTraitAndSuperLaws(
        self: *const Analyzer,
        trait_idx: usize,
        out: *std.ArrayList(TraitLawDef),
    ) std.mem.Allocator.Error!void {
        if (trait_idx >= self.trait_defs.items.len) return;
        const tr = self.trait_defs.items[trait_idx];
        for (tr.supers) |sup| {
            try self.collectTraitAndSuperLaws(sup.trait_idx, out);
        }
        for (tr.laws) |lw| {
            try out.append(self.alloc, .{ .law = lw, .owner_trait_idx = trait_idx });
        }
    }

    fn buildTraitSubstMap(
        self: *Analyzer,
        trait_idx: usize,
        target_tys: []const *const Ty,
        target_hkts: []const ?[]const u8,
    ) std.mem.Allocator.Error!std.StringHashMapUnmanaged(*const Ty) {
        var subst: std.StringHashMapUnmanaged(*const Ty) = .empty;
        if (trait_idx >= self.trait_defs.items.len) return subst;
        const tr = self.trait_defs.items[trait_idx];
        for (tr.params, 0..) |tp, pi| {
            if (tp.arity == 0) {
                if (pi < target_tys.len) {
                    try subst.put(self.alloc, tp.name, target_tys[pi]);
                }
            } else {
                const hn = if (pi < target_hkts.len) target_hkts[pi] else null;
                if (hn) |cname| {
                    const hkey = try std.fmt.allocPrint(self.alloc, "__hkt__{s}", .{tp.name});
                    if (std.mem.eql(u8, cname, "Option")) {
                        try subst.put(self.alloc, hkey, try self.allocTy(.{ .option = try self.allocTy(.err) }));
                    } else if (self.findRecordIndex(cname)) |ri| {
                        try subst.put(self.alloc, hkey, try self.allocTy(.{ .applied = .{ .kind = .record, .decl_idx = ri, .args = &.{} } }));
                    } else if (self.findADTIndex(cname)) |ai| {
                        try subst.put(self.alloc, hkey, try self.allocTy(.{ .applied = .{ .kind = .adt, .decl_idx = ai, .args = &.{} } }));
                    } else {
                        try subst.put(self.alloc, hkey, try self.allocTy(.{ .hkt_app = .{ .ctor = cname, .arg = try self.allocTy(.err) } }));
                    }
                }
            }
        }
        return subst;
    }

    fn instanceTargetsOverlap(self: *Analyzer, prev: InstanceDef, target_tys: []const *const Ty, target_hkts: []const ?[]const u8) bool {
        if (prev.target_tys.len != target_tys.len) return false;
        var subst: std.StringHashMapUnmanaged(*const Ty) = .empty;
        for (prev.target_tys, target_tys, 0..) |pt, nt, i| {
            const ph = if (i < prev.target_hkt_names.len) prev.target_hkt_names[i] else null;
            const nh = if (i < target_hkts.len) target_hkts[i] else null;
            if (ph != null or nh != null) {
                if (ph == null or nh == null) return false;
                if (!std.mem.eql(u8, ph.?, nh.?)) return false;
            } else {
                if (!(self.unifyType(pt, nt, &subst) catch false)) return false;
            }
        }
        return true;
    }

    fn registerInstanceDecl(
        self: *Analyzer,
        decl: ast.Decl,
        decl_idx: usize,
        inst: anytype,
    ) std.mem.Allocator.Error!void {
        _ = decl_idx;
        var inst_cs: std.ArrayList(ResolvedConstraint) = .empty;
        const hkt_mark = self.active_hkt_params.items.len;
        defer self.active_hkt_params.shrinkRetainingCapacity(hkt_mark);
        var inst_hkts: std.ArrayList([]const u8) = .empty;

        for (inst.constraints) |tc| {
            if (try self.resolveTraitConstraint(tc)) |rc| {
                try inst_cs.append(self.alloc, rc);
                const tr = self.trait_defs.items[rc.trait_idx];
                for (rc.hkt_arg_names, 0..) |hn_opt, hi| {
                    if (hi < tr.params.len and tr.params[hi].arity >= 1) {
                        if (hn_opt) |hn| {
                            var is_concrete = std.mem.eql(u8, hn, "Option") or std.mem.eql(u8, hn, "Result");
                            if (!is_concrete and hn.len > 0 and hn[0] >= 'A' and hn[0] <= 'Z') is_concrete = true;
                            if (!is_concrete) {
                                try inst_hkts.append(self.alloc, hn);
                                try self.active_hkt_params.append(self.alloc, hn);
                            }
                        }
                    }
                }
            }
        }

        const tref = (try self.resolveTraitConstraint(inst.trait_ref)) orelse return;
        const tr = self.trait_defs.items[tref.trait_idx];
        const raw_local = if (inst.name) |nm|
            nm.slice(self.source)
        else
            try std.fmt.allocPrint(self.alloc, "__default_{s}_{d}", .{ tr.local_name, self.instance_defs.items.len });
        const cname = try self.canonicalName(self.current_module_id, raw_local, false);
        try self.decl_canonical_names.put(self.alloc, decl.span.start, cname);
        if (self.findInstanceIndex(cname) != null) {
            self.addError(.duplicate_decl, decl.span, "duplicate instance declaration name");
            return;
        }

        if (inst.is_default) {
            for (self.instance_defs.items) |prev| {
                if (prev.is_default and prev.trait_idx == tref.trait_idx and self.instanceTargetsOverlap(prev, tref.args, tref.hkt_arg_names)) {
                    self.addError(.duplicate_decl, decl.span, "ambiguous default instances for trait; only one default instance is permitted per type");
                    break;
                }
            }
        }

        const ext_spec = self.parseExternalRustAttr(decl.attrs, raw_local);
        if (ext_spec) |es| {
            try self.foreign_contracts.append(self.alloc, .{
                .aethel_name = cname,
                .rust_target = es.target orelse tref.hkt_arg_names[0],
                .rust_sym = es.sym,
                .trait_name = tr.name,
                .span = es.span,
            });
        }

        var tparams: std.ArrayList([]const u8) = .empty;
        for (tref.args, 0..) |ta, ti| {
            if (ti < tr.params.len and tr.params[ti].arity == 0) {
                try self.collectTypeVars(ta, &tparams);
            }
        }
        for (inst_cs.items) |rc| {
            const ctr = self.trait_defs.items[rc.trait_idx];
            for (rc.args, 0..) |ca, ci| {
                if (ci < ctr.params.len and ctr.params[ci].arity == 0) {
                    try self.collectTypeVars(ca, &tparams);
                }
            }
        }

        var trait_subst = try self.buildTraitSubstMap(tref.trait_idx, tref.args, tref.hkt_arg_names);
        var req_methods: std.ArrayList(RequiredTraitMethod) = .empty;
        try self.collectTraitAndSuperMethods(tref.trait_idx, &req_methods);

        var has_pure = false;
        var has_bind = false;
        for (inst.methods) |im| {
            const mname = im.name.slice(self.source);
            if (std.mem.eql(u8, mname, "pure")) has_pure = true;
            if (std.mem.eql(u8, mname, "bind")) has_bind = true;
        }

        var checked_methods: std.ArrayList(CheckedInstanceMethod) = .empty;
        for (req_methods.items) |req| {
            var matched_ast: ?ast.InstanceMethod = null;
            for (inst.methods) |im| {
                if (std.mem.eql(u8, im.name.slice(self.source), req.def.name)) {
                    matched_ast = im;
                    break;
                }
            }

            const ptypes = try self.alloc.alloc(*const Ty, req.def.params.len);
            for (req.def.params, 0..) |rp, pi| {
                ptypes[pi] = try self.substituteType(rp, &trait_subst);
            }
            const rty = try self.substituteType(req.def.ret, &trait_subst);

            if (matched_ast) |im| {
                const esym: ?[]const u8 = if (ext_spec != null)
                    try std.fmt.allocPrint(self.alloc, "__aethel_ext_{s}_{s}", .{ cname, req.def.name })
                else
                    null;
                if (ext_spec != null) {
                    for (ptypes, im.params) |pt, ip| self.validateRustFFIType(ip.span, pt, false);
                    self.validateRustFFIType(im.span, rty, true);
                }
                try checked_methods.append(self.alloc, .{
                    .local_name = req.def.name,
                    .params = ptypes,
                    .ret = rty,
                    .type_params = req.def.type_params,
                    .ast_method = im,
                    .synth = .none,
                    .ext_sym = esym,
                });
            } else if (ext_spec != null) {
                const esym = try std.fmt.allocPrint(self.alloc, "__aethel_ext_{s}_{s}", .{ cname, req.def.name });
                for (ptypes) |pt| self.validateRustFFIType(decl.span, pt, false);
                self.validateRustFFIType(decl.span, rty, true);
                try checked_methods.append(self.alloc, .{
                    .local_name = req.def.name,
                    .params = ptypes,
                    .ret = rty,
                    .type_params = req.def.type_params,
                    .ast_method = null,
                    .synth = .none,
                    .ext_sym = esym,
                });
            } else if (has_pure and has_bind and (std.mem.eql(u8, req.def.name, "fmap") or std.mem.eql(u8, req.def.name, "map"))) {
                try checked_methods.append(self.alloc, .{
                    .local_name = req.def.name,
                    .params = ptypes,
                    .ret = rty,
                    .type_params = req.def.type_params,
                    .ast_method = null,
                    .synth = .monad_map,
                });
            } else if (has_pure and has_bind and std.mem.eql(u8, req.def.name, "ap")) {
                try checked_methods.append(self.alloc, .{
                    .local_name = req.def.name,
                    .params = ptypes,
                    .ret = rty,
                    .type_params = req.def.type_params,
                    .ast_method = null,
                    .synth = .monad_ap,
                });
            } else {
                // Delegate supertrait method from a unique default instance of owner_trait_idx if present.
                var found_super: ?CheckedInstanceMethod = null;
                for (self.instance_defs.items) |prev| {
                    if (prev.is_default and prev.trait_idx == req.owner_trait_idx and self.instanceTargetsOverlap(prev, tref.args, tref.hkt_arg_names)) {
                        for (prev.methods) |pm| {
                            if (std.mem.eql(u8, pm.local_name, req.def.name)) {
                                found_super = pm;
                                break;
                            }
                        }
                    }
                    if (found_super != null) break;
                }
                if (found_super) |sm| {
                    try checked_methods.append(self.alloc, sm);
                } else {
                    const msg = try std.fmt.allocPrint(self.alloc, "instance '{s}' is missing required method '{s}'", .{ raw_local, req.def.name });
                    self.addError(.type_mismatch, decl.span, msg);
                }
            }
        }

        try self.instance_defs.append(self.alloc, .{
            .name = cname,
            .local_name = raw_local,
            .module_id = self.current_module_id,
            .is_pub = decl.is_pub,
            .is_default = inst.is_default,
            .is_external_rust = ext_spec != null,
            .rust_target = if (ext_spec) |es| (es.target orelse tref.hkt_arg_names[0]) else null,
            .rust_sym = if (ext_spec) |es| es.sym else null,
            .span = decl.span,
            .decl_ast = decl.kind,
            .trait_idx = tref.trait_idx,
            .target_tys = tref.args,
            .target_hkt_names = tref.hkt_arg_names,
            .type_params = try tparams.toOwnedSlice(self.alloc),
            .hkt_params = try inst_hkts.toOwnedSlice(self.alloc),
            .constraints = try inst_cs.toOwnedSlice(self.alloc),
            .methods = try checked_methods.toOwnedSlice(self.alloc),
        });
    }

    fn instanceMatchesRequirement(
        self: *Analyzer,
        inst_idx: usize,
        req_trait_idx: usize,
        target_tys: []const *const Ty,
        target_hkts: []const ?[]const u8,
        out_subst: *std.StringHashMapUnmanaged(*const Ty),
    ) bool {
        const inst = self.instance_defs.items[inst_idx];
        if (!self.traitHasSuper(inst.trait_idx, req_trait_idx)) return false;
        if (inst.target_tys.len != target_tys.len) return false;
        for (inst.target_tys, target_tys, 0..) |pat, actual, i| {
            const ih = if (i < inst.target_hkt_names.len) inst.target_hkt_names[i] else null;
            const th = if (i < target_hkts.len) target_hkts[i] else null;
            if (ih != null or th != null) {
                if (ih == null or th == null) return false;
                if (!std.mem.eql(u8, ih.?, th.?)) return false;
            } else {
                if (!(self.unifyType(pat, actual, out_subst) catch false)) return false;
            }
        }
        return true;
    }

    fn instantiateConstraintWitness(
        self: *Analyzer,
        inst_idx: usize,
        subst: *const std.StringHashMapUnmanaged(*const Ty),
        span: ast.Span,
        emit_error: bool,
    ) ?ResolvedWitness {
        const inst = self.instance_defs.items[inst_idx];
        var targs = self.alloc.alloc(*const Ty, inst.type_params.len) catch return null;
        for (inst.type_params, 0..) |tp, ti| {
            targs[ti] = subst.get(tp) orelse (self.allocTy(.{ .type_var = tp }) catch return null);
        }
        var subs = self.alloc.alloc(ResolvedWitness, inst.constraints.len) catch return null;
        for (inst.constraints, 0..) |c, ci| {
            var sargs = self.alloc.alloc(*const Ty, c.args.len) catch return null;
            for (c.args, 0..) |a, ai| {
                sargs[ai] = self.substituteType(a, subst) catch a;
            }
            subs[ci] = self.resolveTraitWitness(c.trait_idx, sargs, c.hkt_arg_names, span, emit_error) orelse return null;
        }
        return .{ .concrete = .{
            .inst_idx = inst_idx,
            .type_args = targs,
            .hkt_args = inst.target_hkt_names,
            .sub_witnesses = subs,
        } };
    }

    fn resolveTraitWitness(
        self: *Analyzer,
        trait_idx: usize,
        target_tys: []const *const Ty,
        target_hkts: []const ?[]const u8,
        span: ast.Span,
        emit_error: bool,
    ) ?ResolvedWitness {
        // 1. Explicit `using` overrides in lexical stack (supports direct + supertrait forgetful functor).
        var ui = self.active_using_stack.items.len;
        while (ui > 0) {
            ui -= 1;
            for (self.active_using_stack.items[ui]) |u_inst_idx| {
                var subst: std.StringHashMapUnmanaged(*const Ty) = .empty;
                if (self.instanceMatchesRequirement(u_inst_idx, trait_idx, target_tys, target_hkts, &subst)) {
                    return self.instantiateConstraintWitness(u_inst_idx, &subst, span, emit_error);
                }
            }
        }

        // 2. Active `with` dictionary parameters in the current generic fn/instance.
        for (self.active_constraints, 0..) |ac, pi| {
            if (!self.traitHasSuper(ac.trait_idx, trait_idx)) continue;
            if (ac.args.len != target_tys.len) continue;
            var all_match = true;
            for (ac.args, target_tys, 0..) |aa, ta, ai| {
                const ah = if (ai < ac.hkt_arg_names.len) ac.hkt_arg_names[ai] else null;
                const th = if (ai < target_hkts.len) target_hkts[ai] else null;
                if (ah != null or th != null) {
                    if (ah == null or th == null or !std.mem.eql(u8, ah.?, th.?)) {
                        all_match = false;
                        break;
                    }
                } else if (!aa.eql(ta.*)) {
                    all_match = false;
                    break;
                }
            }
            if (all_match) return .{ .param = pi };
        }

        // 3. Open-universe visible `default instance` (exact trait first, then forgetful subtraits `<=`).
        const MatchItem = struct { idx: usize, subst: std.StringHashMapUnmanaged(*const Ty) };
        var matches: std.ArrayList(MatchItem) = .empty;
        for (self.instance_defs.items, 0..) |inst, idx| {
            if (!inst.is_default or inst.trait_idx != trait_idx) continue;
            var subst: std.StringHashMapUnmanaged(*const Ty) = .empty;
            if (self.instanceMatchesRequirement(idx, trait_idx, target_tys, target_hkts, &subst)) {
                matches.append(self.alloc, .{ .idx = idx, .subst = subst }) catch {};
            }
        }
        if (matches.items.len > 1) {
            var filtered: std.ArrayList(MatchItem) = .empty;
            for (matches.items) |m| {
                var subst_copy = m.subst.clone(self.alloc) catch continue;
                if (self.instantiateConstraintWitness(m.idx, &subst_copy, span, false) != null) {
                    filtered.append(self.alloc, m) catch {};
                }
            }
            if (filtered.items.len > 0) matches = filtered;
        }
        if (matches.items.len == 0) {
            for (self.instance_defs.items, 0..) |inst, idx| {
                if (!inst.is_default or inst.trait_idx == trait_idx) continue;
                var subst: std.StringHashMapUnmanaged(*const Ty) = .empty;
                if (self.instanceMatchesRequirement(idx, trait_idx, target_tys, target_hkts, &subst)) {
                    var subst_copy = subst.clone(self.alloc) catch continue;
                    if (self.instantiateConstraintWitness(idx, &subst_copy, span, false) != null) {
                        matches.append(self.alloc, .{ .idx = idx, .subst = subst }) catch {};
                    }
                }
            }
            // Prefer the most general supertrait when multiple subtraits implement the same target
            // (e.g. Ring(Complex(a)) over Field(Complex(a)) when resolving Semiring(Complex(f64))).
            if (matches.items.len > 1) {
                var best: std.ArrayList(MatchItem) = .empty;
                for (matches.items, 0..) |mi, i| {
                    const ti = self.instance_defs.items[mi.idx].trait_idx;
                    var has_super_candidate = false;
                    for (matches.items, 0..) |mj, j| {
                        if (i == j) continue;
                        const tj = self.instance_defs.items[mj.idx].trait_idx;
                        if (ti != tj and self.traitHasSuper(ti, tj)) {
                            has_super_candidate = true;
                            break;
                        }
                    }
                    if (!has_super_candidate) {
                        best.append(self.alloc, mi) catch {};
                    }
                }
                if (best.items.len > 0) matches = best;
            }
        }
        if (matches.items.len == 1) {
            return self.instantiateConstraintWitness(matches.items[0].idx, &matches.items[0].subst, span, emit_error);
        }
        if (matches.items.len > 1) {
            if (emit_error) self.addError(.borrow_conflict, span, "ambiguous default instances satisfy trait constraint; use 'using' to select one");
            return null;
        }
        if (emit_error) self.addError(.type_mismatch, span, "no matching default instance found for trait constraint");
        return null;
    }

    fn checkTraitLawsWellTyped(self: *Analyzer, span: ast.Span, tr: anytype) std.mem.Allocator.Error!void {
        _ = span;
        const tidx = self.findTraitInModule(self.current_module_id, tr.name.slice(self.source)) orelse return;
        const tdef = self.trait_defs.items[tidx];
        const prev_constraints = self.active_constraints;
        const hkt_mark = self.active_hkt_params.items.len;
        for (tdef.params) |tp| {
            if (tp.arity >= 1) try self.active_hkt_params.append(self.alloc, tp.name);
        }
        var cs_buf: [1]ResolvedConstraint = undefined;
        const p_args = try self.alloc.alloc(*const Ty, tdef.params.len);
        const p_hkts = try self.alloc.alloc(?[]const u8, tdef.params.len);
        for (tdef.params, 0..) |tp, pi| {
            p_args[pi] = try self.allocTy(.{ .type_var = tp.name });
            p_hkts[pi] = if (tp.arity >= 1) tp.name else null;
        }
        cs_buf[0] = .{ .trait_idx = tidx, .args = p_args, .hkt_arg_names = p_hkts };
        self.active_constraints = &cs_buf;
        defer {
            self.active_constraints = prev_constraints;
            self.active_hkt_params.shrinkRetainingCapacity(hkt_mark);
        }

        for (tr.laws) |lw| {
            try self.pushScope();
            defer self.popScope();
            for (lw.params) |p| {
                const pty = if (p.ty) |t| try self.resolveType(t) else try self.allocTy(.err);
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
            for (lw.clauses) |cl| {
                switch (cl) {
                    .when => |wh| _ = try self.checkExpr(wh.expr, try self.allocTy(.bool)),
                    .always => |a| _ = try self.checkExpr(a.expr, try self.allocTy(.bool)),
                    .never => |n| _ = try self.checkExpr(n.expr, try self.allocTy(.bool)),
                    .expr => |e| _ = try self.checkExpr(e.expr, try self.allocTy(.bool)),
                    .preserves => {},
                }
            }
        }
    }

    fn checkInstanceBodies(self: *Analyzer, span: ast.Span, inst_ast: anytype) std.mem.Allocator.Error!void {
        _ = span;
        var matched_inst: ?*const InstanceDef = null;
        for (self.instance_defs.items) |*id| {
            if (id.module_id == self.current_module_id and id.decl_ast == .instance_decl and id.span.start == self.findDeclStartByAst(inst_ast)) {
                matched_inst = id;
                break;
            }
        }
        const idef = matched_inst orelse return;
        if (idef.is_external_rust) return;

        const prev_constraints = self.active_constraints;
        const hkt_mark = self.active_hkt_params.items.len;
        self.active_constraints = idef.constraints;
        for (idef.hkt_params) |hp| try self.active_hkt_params.append(self.alloc, hp);
        defer {
            self.active_constraints = prev_constraints;
            self.active_hkt_params.shrinkRetainingCapacity(hkt_mark);
        }

        for (idef.methods) |cm| {
            const im = cm.ast_method orelse continue;
            try self.pushScope();
            defer self.popScope();

            for (im.params, 0..) |p, pi| {
                const pty = if (pi < cm.params.len) cm.params[pi] else try self.allocTy(.err);
                try self.scopes.append(self.alloc, .{
                    .name = p.name.slice(self.source),
                    .ty = pty,
                    .range = pty.rangeOf(),
                    .mutable = p.mutable,
                    .moved = false,
                    .authorized_paths = null,
                    .decl_span = p.span,
                    .is_param = true,
                    .param_index = pi,
                });
            }

            const prev_ret = self.current_fn_ret;
            self.current_fn_ret = cm.ret;
            defer self.current_fn_ret = prev_ret;

            const body_res = try self.checkBlock(&im.body, cm.ret, im.ret != null);
            if (!cm.ret.eql(.unit) and (im.body.tail != null or im.body.stmts.len == 0)) {
                try self.checkAssignmentValue(im.body.span, cm.ret, body_res);
            }
        }
    }

    fn findDeclStartByAst(self: *const Analyzer, inst_ast: anytype) usize {
        for (self.module.decls) |decl| {
            if (decl.kind == .instance_decl and decl.kind.instance_decl.trait_ref.span.start == inst_ast.trait_ref.span.start) {
                return decl.span.start;
            }
        }
        return 0;
    }

    fn resolveAllTypeSignatures(self: *Analyzer) std.mem.Allocator.Error!void {
        // Resolve type aliases first so records/functions/traits can reference aliases in any order.
        for (self.module.decls) |decl| {
            self.current_module_id = self.moduleIdOfSpan(decl.span);
            if (decl.kind == .type_decl and decl.kind.type_decl.body == .alias) {
                const td = decl.kind.type_decl;
                const local_name = td.name.slice(self.source);
                const resolved = try self.resolveType(td.body.alias);
                const cname = self.decl_canonical_names.get(decl.span.start) orelse local_name;
                try self.type_aliases.put(self.alloc, cname, resolved);
                for (self.type_alias_entries.items) |*ta| {
                    if (ta.module_id == self.current_module_id and std.mem.eql(u8, ta.local_name, local_name)) {
                        ta.ty = resolved;
                        break;
                    }
                }
            }
        }

        // Resolve trait supertraits & method signatures before instances and functions.
        for (self.module.decls) |decl| {
            self.current_module_id = self.moduleIdOfSpan(decl.span);
            if (decl.kind != .trait_decl) continue;
            const tr = decl.kind.trait_decl;
            const local_name = tr.name.slice(self.source);
            const tidx = self.findTraitInModule(self.current_module_id, local_name) orelse continue;

            const hkt_mark = self.active_hkt_params.items.len;
            defer self.active_hkt_params.shrinkRetainingCapacity(hkt_mark);
            for (self.trait_defs.items[tidx].params) |tp| {
                if (tp.arity >= 1) try self.active_hkt_params.append(self.alloc, tp.name);
            }

            var sups: std.ArrayList(ResolvedConstraint) = .empty;
            for (tr.supers) |sc| {
                if (try self.resolveTraitConstraint(sc)) |rc| {
                    try sups.append(self.alloc, rc);
                }
            }
            var mdefs: std.ArrayList(TraitMethodDef) = .empty;
            for (tr.methods) |msig| {
                const mname = msig.name.slice(self.source);
                const ptypes = try self.alloc.alloc(*const Ty, msig.params.len);
                const pnames = try self.alloc.alloc([]const u8, msig.params.len);
                var tparams: std.ArrayList([]const u8) = .empty;
                for (msig.params, 0..) |p, pi| {
                    pnames[pi] = p.name.slice(self.source);
                    ptypes[pi] = if (p.ty) |t| try self.resolveType(t) else try self.allocTy(.err);
                    try self.collectTypeVars(ptypes[pi], &tparams);
                }
                const rty = if (msig.ret) |rt| try self.resolveType(rt) else try self.allocTy(.unit);
                try self.collectTypeVars(rty, &tparams);
                // Filter out trait-level parameters (they are fixed by the trait instance itself).
                var extra_tparams: std.ArrayList([]const u8) = .empty;
                for (tparams.items) |tv| {
                    var is_trait_param = false;
                    for (self.trait_defs.items[tidx].params) |tp| {
                        if (std.mem.eql(u8, tp.name, tv)) {
                            is_trait_param = true;
                            break;
                        }
                    }
                    if (!is_trait_param) try extra_tparams.append(self.alloc, tv);
                }
                try mdefs.append(self.alloc, .{
                    .name = mname,
                    .sig = msig,
                    .param_names = pnames,
                    .params = ptypes,
                    .ret = rty,
                    .type_params = try extra_tparams.toOwnedSlice(self.alloc),
                });
            }
            self.trait_defs.items[tidx].supers = try sups.toOwnedSlice(self.alloc);
            self.trait_defs.items[tidx].methods = try mdefs.toOwnedSlice(self.alloc);
        }

        // Resolve record fields, ADT variants, and type_decl constraints.
        for (self.module.decls) |decl| {
            self.current_module_id = self.moduleIdOfSpan(decl.span);
            switch (decl.kind) {
                .type_decl => |td| {
                    const name = td.name.slice(self.source);
                    var cs_list: std.ArrayList(ResolvedConstraint) = .empty;
                    for (td.constraints) |tc| {
                        if (try self.resolveTraitConstraint(tc)) |rc| {
                            try cs_list.append(self.alloc, rc);
                        }
                    }
                    const cs_slice = try cs_list.toOwnedSlice(self.alloc);
                    switch (td.body) {
                        .alias => {},
                        .record => |fields| {
                            if (self.findRecordInModule(self.current_module_id, name)) |ridx| {
                                self.record_defs.items[ridx].constraints = cs_slice;
                                const is_flat = self.record_defs.items[ridx].is_flat_c;
                                for (fields, 0..) |rf, fi| {
                                    const fty = try self.resolveType(rf.ty);
                                    const info = self.typeBitInfo(fty);
                                    const fattrs = try self.parseRustHelperAttrs(rf.attrs, is_flat);
                                    self.record_defs.items[ridx].fields[fi] = .{
                                        .name = rf.name.slice(self.source),
                                        .ty = fty,
                                        .bits = info.bits,
                                        .signed = info.signed,
                                        .mutable = rf.mutable,
                                        .rust_attrs = fattrs,
                                    };
                                }
                                self.record_defs.items[ridx].fields_resolved = true;
                            }
                        },
                        .variants => |variants| {
                            if (self.findADTInModule(self.current_module_id, name)) |aidx| {
                                self.adt_defs.items[aidx].constraints = cs_slice;
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

        // Resolve function, extern, and instance signatures.
        for (self.module.decls, 0..) |decl, decl_idx| {
            self.current_module_id = self.moduleIdOfSpan(decl.span);
            switch (decl.kind) {
                .fn_decl => |fd| {
                    const local_name = fd.name.slice(self.source);
                    if (self.findFnInModule(self.current_module_id, local_name) != null) {
                        self.addError(.duplicate_decl, fd.name, "duplicate function declaration");
                        continue;
                    }
                    const cname = try self.canonicalName(self.current_module_id, local_name, false);
                    try self.decl_canonical_names.put(self.alloc, decl.span.start, cname);

                    var fn_cs: std.ArrayList(ResolvedConstraint) = .empty;
                    const hkt_mark = self.active_hkt_params.items.len;
                    defer self.active_hkt_params.shrinkRetainingCapacity(hkt_mark);
                    var fn_hkts: std.ArrayList([]const u8) = .empty;
                    for (fd.constraints) |tc| {
                        if (try self.resolveTraitConstraint(tc)) |rc| {
                            try fn_cs.append(self.alloc, rc);
                            const tr = self.trait_defs.items[rc.trait_idx];
                            for (rc.hkt_arg_names, 0..) |hn_opt, hi| {
                                if (hi < tr.params.len and tr.params[hi].arity >= 1) {
                                    if (hn_opt) |hn| {
                                        var is_concrete_ctor = std.mem.eql(u8, hn, "Option") or std.mem.eql(u8, hn, "Result");
                                        if (!is_concrete_ctor and hn.len > 0 and hn[0] >= 'A' and hn[0] <= 'Z') is_concrete_ctor = true;
                                        if (!is_concrete_ctor) {
                                            var seen_h = false;
                                            for (fn_hkts.items) |prev| if (std.mem.eql(u8, prev, hn)) {
                                                seen_h = true;
                                            };
                                            if (!seen_h) {
                                                try fn_hkts.append(self.alloc, hn);
                                                try self.active_hkt_params.append(self.alloc, hn);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }

                    const ext_spec = self.parseExternalRustAttr(decl.attrs, local_name);
                    if (!fd.has_body and ext_spec == null) {
                        self.addError(.invalid_ffi_type, fd.name, "bodyless function requires @external(rust, ...) attribute");
                    }

                    const prev_c_fn = self.active_constraints;
                    self.active_constraints = fn_cs.items;
                    defer self.active_constraints = prev_c_fn;

                    const ptypes = try self.alloc.alloc(*const Ty, fd.params.len);
                    const pauths = try self.alloc.alloc(?[]const usize, fd.params.len);
                    var target_rec: ?usize = null;
                    for (fd.params, 0..) |p, pi| {
                        const rty = if (p.ty) |t| try self.resolveType(t) else try self.allocTy(.err);
                        ptypes[pi] = rty;
                        pauths[pi] = try self.extractAuthorizedPaths(p.span, rty);
                        if (target_rec == null) target_rec = recordOfType(rty);
                        if (ext_spec != null) self.validateRustFFIType(p.span, rty, false);
                    }
                    const rty = if (fd.ret) |rt| try self.resolveType(rt) else try self.allocTy(.unit);
                    if (ext_spec != null) self.validateRustFFIType(fd.name, rty, true);

                    var tparams: std.ArrayList([]const u8) = .empty;
                    for (ptypes) |pt| try self.collectTypeVars(pt, &tparams);
                    try self.collectTypeVars(rty, &tparams);
                    for (fn_cs.items) |rc| {
                        const tr = self.trait_defs.items[rc.trait_idx];
                        for (rc.args, 0..) |ca, ci| {
                            if (ci < tr.params.len and tr.params[ci].arity == 0) {
                                try self.collectTypeVars(ca, &tparams);
                            }
                        }
                    }

                    var c_abi_sym: ?[]const u8 = if (ext_spec) |es| es.sym else null;
                    if (ext_spec) |es| {
                        if (es.target) |tgt| {
                            if (self.declared_rust_crates) |declared| {
                                if (!self.isDeclaredRustTarget(tgt, declared)) {
                                    const msg = try std.fmt.allocPrint(
                                        self.alloc,
                                        "undeclared Rust crate '{s}' in @external(rust, ...): add it to [rust-dependencies] via 'aethel add --rust {s}'",
                                        .{ tgt, tgt },
                                    );
                                    self.addError(.invalid_ffi_type, es.span, msg);
                                }
                            }
                            c_abi_sym = try self.sanitizeRustExtSym(tgt, es.sym);
                        }
                        try self.foreign_contracts.append(self.alloc, .{
                            .aethel_name = cname,
                            .rust_target = es.target,
                            .rust_sym = es.sym,
                            .span = es.span,
                        });
                    }

                    try self.fn_sigs.append(self.alloc, .{
                        .name = cname,
                        .local_name = local_name,
                        .module_id = self.current_module_id,
                        .is_pub = decl.is_pub,
                        .span = fd.name,
                        .type_params = try tparams.toOwnedSlice(self.alloc),
                        .hkt_params = try fn_hkts.toOwnedSlice(self.alloc),
                        .constraints = try fn_cs.toOwnedSlice(self.alloc),
                        .params = ptypes,
                        .param_auths = pauths,
                        .ret = rty,
                        .target_record = target_rec,
                        .is_extern = ext_spec != null,
                        .has_body = fd.has_body,
                        .rust_target = if (ext_spec) |es| es.target else null,
                        .rust_sym = c_abi_sym,
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
                            self.validateRustFFIType(p.span, rty, false);
                        }
                        const rty = if (ef.ret) |rt| try self.resolveType(rt) else try self.allocTy(.unit);
                        self.validateRustFFIType(ef.span, rty, true);
                        try self.foreign_contracts.append(self.alloc, .{
                            .aethel_name = name,
                            .rust_target = null,
                            .rust_sym = name,
                            .span = ef.span,
                        });
                        try self.fn_sigs.append(self.alloc, .{
                            .name = name,
                            .local_name = name,
                            .module_id = self.current_module_id,
                            .is_pub = decl.is_pub or ef.is_pub,
                            .span = ef.name,
                            .params = ptypes,
                            .param_auths = pauths,
                            .ret = rty,
                            .target_record = null,
                            .is_extern = true,
                            .has_body = false,
                            .rust_sym = name,
                            .decl_index = null,
                        });
                    }
                },
                .instance_decl => |inst| {
                    try self.registerInstanceDecl(decl, decl_idx, inst);
                },
                else => {},
            }
        }
    }

    fn isFlatCABIScalarOrRecord(self: *Analyzer, span: ast.Span, ty: *const Ty, depth: u8) bool {
        if (depth > 8) return false;
        return switch (ty.*) {
            .bool, .f32, .f64, .opaque_ty, .err => true,
            .int => |it| blk: {
                if (it.bits != 8 and it.bits != 16 and it.bits != 32 and it.bits != 64 and it.bits != 128) {
                    self.addError(.invalid_ffi_type, span, "Rust FFI scalar integer must be ABI byte width (8, 16, 32, 64, or 128 bits)");
                    break :blk false;
                }
                break :blk true;
            },
            .int_range => {
                self.addError(.invalid_ffi_type, span, "Rust FFI flat struct forbids sub-byte Int(...) range fields; use fixed-width scalars (u8..u128, i8..i128)");
                return false;
            },
            .record => |ridx| blk: {
                const rdef = &self.record_defs.items[ridx];
                if (rdef.is_packed_attr) {
                    self.addError(.invalid_ffi_type, span, "Rust FFI forbids @layout(packed) records; use @layout(flat), @layout(soa), or @layout(aosoa(W))");
                    break :blk false;
                }
                for (rdef.fields) |f| {
                    if (!self.isFlatCABIScalarOrRecord(span, f.ty, depth + 1)) break :blk false;
                }
                rdef.is_flat_c = true;
                break :blk true;
            },
            else => false,
        };
    }

    fn unescapeRustAttrString(self: *Analyzer, raw_quoted: []const u8) std.mem.Allocator.Error![]const u8 {
        const inner = stripStringQuotes(raw_quoted);
        var buf: std.ArrayList(u8) = .empty;
        var i: usize = 0;
        while (i < inner.len) : (i += 1) {
            if (inner[i] == '\\' and i + 1 < inner.len) {
                i += 1;
                switch (inner[i]) {
                    'n' => try buf.append(self.alloc, '\n'),
                    'r' => try buf.append(self.alloc, '\r'),
                    't' => try buf.append(self.alloc, '\t'),
                    '\\' => try buf.append(self.alloc, '\\'),
                    '"' => try buf.append(self.alloc, '"'),
                    else => try buf.append(self.alloc, inner[i]),
                }
            } else {
                try buf.append(self.alloc, inner[i]);
            }
        }
        return try buf.toOwnedSlice(self.alloc);
    }

    fn isAllowedRustHelperNamespace(ns: []const u8) bool {
        return std.mem.eql(u8, ns, "serde") or
            std.mem.eql(u8, ns, "component") or
            std.mem.eql(u8, ns, "bytemuck") or
            std.mem.eql(u8, ns, "reflect") or
            std.mem.eql(u8, ns, "bincode");
    }

    fn extractRustAttrNamespace(attr_text: []const u8) []const u8 {
        const trimmed = std.mem.trim(u8, attr_text, " \t\r\n");
        var end: usize = 0;
        while (end < trimmed.len) : (end += 1) {
            const c = trimmed[end];
            if (c == '(' or c == '=' or c == ' ' or c == '\t' or c == ':') break;
        }
        return trimmed[0..end];
    }

    fn isValidRustTraitPath(s: []const u8) bool {
        if (s.len == 0) return false;
        for (s) |c| {
            const ok = (c >= 'a' and c <= 'z') or
                (c >= 'A' and c <= 'Z') or
                (c >= '0' and c <= '9') or
                c == '_' or c == ':';
            if (!ok) return false;
        }
        return true;
    }

    const ParsedRustRecordAttrs = struct {
        derives: []const []const u8,
        attrs: []const []const u8,
        has_pod_derive: bool,
    };

    fn parseRustHelperAttrs(
        self: *Analyzer,
        attrs: []const ast.Attribute,
        is_flat_record: bool,
    ) std.mem.Allocator.Error![]const []const u8 {
        var out: std.ArrayList([]const u8) = .empty;
        for (attrs) |attr| {
            const aname = attr.name.slice(self.source);
            if (!std.mem.eql(u8, aname, "rust_attr")) continue;
            if (!is_flat_record) {
                self.addError(.invalid_ffi_type, attr.span, "@rust_attr requires enclosing @layout(flat) record");
                continue;
            }
            if (attr.payload != .args or attr.payload.args.len == 0) {
                self.addError(.invalid_ffi_type, attr.span, "@rust_attr expects one or more string helper attributes");
                continue;
            }
            for (attr.payload.args) |arg_expr| {
                if (arg_expr.* != .string_lit) {
                    self.addError(.invalid_ffi_type, arg_expr.getSpan(), "@rust_attr arguments must be string literals");
                    continue;
                }
                const txt = try self.unescapeRustAttrString(arg_expr.string_lit.slice(self.source));
                const ns = extractRustAttrNamespace(txt);
                if (!isAllowedRustHelperNamespace(ns)) {
                    self.addError(.invalid_ffi_type, attr.span, "@rust_attr only permits inert derive helpers (serde, component, bytemuck, reflect, bincode); layout-altering attributes like repr(...) are forbidden");
                    continue;
                }
                try out.append(self.alloc, txt);
            }
        }
        return try out.toOwnedSlice(self.alloc);
    }

    fn parseRustRecordAttrs(
        self: *Analyzer,
        attrs: []const ast.Attribute,
        is_flat: bool,
    ) std.mem.Allocator.Error!ParsedRustRecordAttrs {
        var derives: std.ArrayList([]const u8) = .empty;
        var has_pod = false;
        for (attrs) |attr| {
            const aname = attr.name.slice(self.source);
            const is_derive = std.mem.eql(u8, aname, "derive");
            const is_rust_derive = std.mem.eql(u8, aname, "rust_derive");
            if (!is_derive and !is_rust_derive) continue;
            if (!is_flat) {
                self.addError(.invalid_ffi_type, attr.span, "@derive(rust, ...) requires @layout(flat) so Zig and Rust share identical #[repr(C)] layout");
                continue;
            }
            if (attr.payload != .args or attr.payload.args.len == 0) {
                self.addError(.invalid_ffi_type, attr.span, "@derive requires target language and trait paths, e.g. @derive(rust, \"serde::Serialize\")");
                continue;
            }
            var start_idx: usize = 0;
            if (is_derive) {
                const lang_expr = attr.payload.args[0];
                const lang = switch (lang_expr.*) {
                    .ident => |sp| sp.slice(self.source),
                    .string_lit => |sp| stripStringQuotes(sp.slice(self.source)),
                    else => "",
                };
                if (!std.mem.eql(u8, lang, "rust")) {
                    self.addError(.invalid_ffi_type, attr.span, "unsupported @derive target (use @derive(rust, ...))");
                    continue;
                }
                start_idx = 1;
            }
            if (start_idx >= attr.payload.args.len) {
                self.addError(.invalid_ffi_type, attr.span, "@derive(rust, ...) requires at least one trait path");
                continue;
            }
            for (attr.payload.args[start_idx..]) |arg_expr| {
                const raw_trait = switch (arg_expr.*) {
                    .string_lit => |sp| try self.unescapeRustAttrString(sp.slice(self.source)),
                    .ident, .upper_ident => |sp| sp.slice(self.source),
                    else => "",
                };
                const trait_path = std.mem.trim(u8, raw_trait, " \t\r\n");
                if (!isValidRustTraitPath(trait_path)) {
                    self.addError(.invalid_ffi_type, arg_expr.getSpan(), "invalid Rust trait path in @derive(rust, ...)");
                    continue;
                }
                const stripped = std.mem.trimStart(u8, trait_path, ":");
                if (std.mem.indexOf(u8, stripped, "::")) |col_idx| {
                    const root_crate = stripped[0..col_idx];
                    const is_std_root = std.mem.eql(u8, root_crate, "core") or
                        std.mem.eql(u8, root_crate, "std") or
                        std.mem.eql(u8, root_crate, "alloc");
                    if (!is_std_root) {
                        if (self.declared_rust_crates) |declared| {
                            if (!self.isDeclaredRustTarget(root_crate, declared)) {
                                const msg = try std.fmt.allocPrint(
                                    self.alloc,
                                    "undeclared Rust crate '{s}' in @derive(rust, ...): add it to [rust-dependencies] via 'aethel add --rust {s}'",
                                    .{ root_crate, root_crate },
                                );
                                self.addError(.invalid_ffi_type, arg_expr.getSpan(), msg);
                            }
                        }
                    }
                }
                if (std.mem.eql(u8, trait_path, "Pod") or std.mem.endsWith(u8, trait_path, "::Pod")) {
                    has_pod = true;
                }
                try derives.append(self.alloc, trait_path);
            }
        }
        const rust_attrs = try self.parseRustHelperAttrs(attrs, is_flat);
        return .{
            .derives = try derives.toOwnedSlice(self.alloc),
            .attrs = rust_attrs,
            .has_pod_derive = has_pod,
        };
    }

    fn isPodBitPatternSafeTy(self: *const Analyzer, ty: *const Ty, depth: u8) bool {
        if (depth > 8) return false;
        return switch (ty.*) {
            .f32, .f64, .err => true,
            .int => |it| it.bits == 8 or it.bits == 16 or it.bits == 32 or it.bits == 64 or it.bits == 128,
            .record => |ridx| blk: {
                const rdef = &self.record_defs.items[ridx];
                if (!rdef.is_flat_c or rdef.fields.len == 0) break :blk false;
                for (rdef.fields) |f| {
                    if (!self.isPodBitPatternSafeTy(f.ty, depth + 1)) break :blk false;
                }
                break :blk true;
            },
            else => false,
        };
    }

    fn rustCrateNamesMatch(a: []const u8, b: []const u8) bool {
        if (a.len != b.len) return false;
        for (a, b) |ca, cb| {
            const na = if (ca == '-') @as(u8, '_') else ca;
            const nb = if (cb == '-') @as(u8, '_') else cb;
            if (na != nb) return false;
        }
        return true;
    }

    fn isDeclaredRustTarget(self: *const Analyzer, target: []const u8, declared: []const []const u8) bool {
        if (std.mem.eql(u8, target, "self") or std.mem.eql(u8, target, "bridge")) return true;
        if (self.project_pkg_name) |pn| {
            if (rustCrateNamesMatch(target, pn)) return true;
        }
        for (declared) |cr| {
            if (rustCrateNamesMatch(target, cr)) return true;
        }
        return false;
    }

    fn sanitizeRustExtSym(self: *Analyzer, target: []const u8, sym: []const u8) std.mem.Allocator.Error![]const u8 {
        var buf: std.ArrayList(u8) = .empty;
        try buf.appendSlice(self.alloc, "ext_");
        for (target) |c| {
            if ((c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or (c >= '0' and c <= '9') or c == '_') {
                try buf.append(self.alloc, c);
            } else {
                try buf.append(self.alloc, '_');
            }
        }
        try buf.appendSlice(self.alloc, "__");
        for (sym) |c| {
            if ((c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or (c >= '0' and c <= '9') or c == '_') {
                try buf.append(self.alloc, c);
            } else {
                try buf.append(self.alloc, '_');
            }
        }
        return try buf.toOwnedSlice(self.alloc);
    }

    fn isValidRustFFISliceElem(self: *Analyzer, span: ast.Span, elem: *const Ty) bool {
        return switch (elem.*) {
            .int => |it| it.bits == 8 or it.bits == 16 or it.bits == 32 or it.bits == 64,
            .f32, .f64 => true,
            .record => |ridx| blk: {
                const rdef = &self.record_defs.items[ridx];
                if (!rdef.is_flat_c) break :blk false;
                break :blk self.isFlatCABIScalarOrRecord(span, elem, 0);
            },
            else => false,
        };
    }

    fn validateRustFFICallbackParam(self: *Analyzer, span: ast.Span, ty: *const Ty) void {
        switch (ty.*) {
            .bool, .f32, .f64, .opaque_ty, .string, .err => {},
            .int => |it| {
                if (it.bits != 8 and it.bits != 16 and it.bits != 32 and it.bits != 64 and it.bits != 128) {
                    self.addError(.invalid_ffi_type, span, "Rust FFI callback scalar integer must be ABI byte width (8, 16, 32, 64, or 128 bits)");
                }
            },
            .record => |ridx| {
                const rdef = &self.record_defs.items[ridx];
                if (!rdef.is_flat_c) {
                    self.addError(.invalid_ffi_type, span, "Rust FFI callback record parameter requires @layout(flat)");
                    return;
                }
                _ = self.isFlatCABIScalarOrRecord(span, ty, 0);
            },
            .view => |v| {
                if (v.target.* == .record) {
                    const rdef = &self.record_defs.items[v.target.record];
                    if (!rdef.is_flat_c) {
                        self.addError(.invalid_ffi_type, span, "Rust FFI callback View parameter requires @layout(flat) record");
                        return;
                    }
                    _ = self.isFlatCABIScalarOrRecord(span, v.target, 0);
                    return;
                }
                if (v.target.* == .slice) {
                    if (!self.isValidRustFFISliceElem(span, v.target.slice.elem)) {
                        self.addError(.invalid_ffi_type, span, "Rust FFI callback slice view requires byte-aligned C-ABI scalar or @layout(flat) record element");
                    }
                    return;
                }
                self.addError(.invalid_ffi_type, span, "unsupported callback View parameter across Aethel -> Rust FFI (use View(FlatRecord, ...) or slice view)");
            },
            .slice => |sl| {
                if (!self.isValidRustFFISliceElem(span, sl.elem)) {
                    self.addError(.invalid_ffi_type, span, "Rust FFI callback slice requires byte-aligned C-ABI scalar or @layout(flat) record element");
                }
            },
            else => {
                self.addError(.invalid_ffi_type, span, "unsupported callback parameter type across Aethel -> Rust FFI (use scalars, String, @opaque, @layout(flat) records, Views, or C-ABI slices)");
            },
        }
    }

    fn validateRustFFIType(self: *Analyzer, span: ast.Span, ty: *const Ty, is_return: bool) void {
        switch (ty.*) {
            .bool, .f32, .f64, .unit, .opaque_ty, .err => {},
            .string => {
                if (is_return) {
                    self.addError(.invalid_ffi_type, span, "Rust FFI function cannot return borrowed String (&str) by value; pass an explicit buffer or callback");
                }
            },
            .fn_ty => |ft| {
                if (is_return) {
                    self.addError(.invalid_ffi_type, span, "Rust FFI function cannot return a callback value");
                    return;
                }
                if (ft.is_once) {
                    self.addError(.invalid_ffi_type, span, "Aethel -> Rust FFI callback cannot be fn_once; foreign schedules require stateless reusable fn(...)");
                    return;
                }
                for (ft.params) |p| {
                    self.validateRustFFICallbackParam(span, p);
                }
                switch (ft.ret.*) {
                    .unit, .bool, .f32, .f64, .opaque_ty, .err => {},
                    .int => |it| {
                        if (it.bits != 8 and it.bits != 16 and it.bits != 32 and it.bits != 64 and it.bits != 128) {
                            self.addError(.invalid_ffi_type, span, "Rust FFI callback return scalar integer must be ABI byte width (8, 16, 32, 64, or 128 bits)");
                        }
                    },
                    .record => |ridx| {
                        const rdef = &self.record_defs.items[ridx];
                        if (!rdef.is_flat_c) {
                            self.addError(.invalid_ffi_type, span, "Rust FFI callback return record requires @layout(flat)");
                        } else {
                            _ = self.isFlatCABIScalarOrRecord(span, ft.ret, 0);
                        }
                    },
                    else => {
                        self.addError(.invalid_ffi_type, span, "unsupported callback return type across Aethel -> Rust FFI (use unit, scalar, @opaque, or @layout(flat) record)");
                    },
                }
            },
            .slice => |sl| {
                if (!self.isValidRustFFISliceElem(span, sl.elem)) {
                    self.addError(.invalid_ffi_type, span, "Rust FFI slice requires byte-aligned C-ABI scalar or @layout(flat) record element (sub-byte packed slices are forbidden)");
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
            .record => |ridx| {
                const rdef = &self.record_defs.items[ridx];
                if (!rdef.is_flat_c) {
                    self.addError(.invalid_ffi_type, span, "Rust FFI record parameter requires @layout(flat) for deterministic C-ABI layout");
                    return;
                }
                _ = self.isFlatCABIScalarOrRecord(span, ty, 0);
            },
            .collection => |c| {
                if (c.elem_record) |ridx| {
                    const rdef = &self.record_defs.items[ridx];
                    const has_phys_col = rdef.collection_layout != null and (rdef.collection_layout.? == .soa or rdef.collection_layout.? == .aosoa);
                    if (!rdef.is_flat_c and !has_phys_col) {
                        self.addError(.invalid_ffi_type, span, "Rust FFI Collection requires @layout(flat), @layout(soa), or @layout(aosoa(W)) element record");
                        return;
                    }
                    const was_flat = rdef.is_flat_c;
                    const rec_ty = self.allocTy(.{ .record = ridx }) catch return;
                    _ = self.isFlatCABIScalarOrRecord(span, rec_ty, 0);
                    rdef.is_flat_c = was_flat;
                } else {
                    self.validateRustFFIType(span, c.elem_ty, is_return);
                }
            },
            .path_borrow => |pb| {
                if (pb.base.* == .collection) {
                    self.validateRustFFIType(span, pb.base, is_return);
                    return;
                }
                if (recordOfType(pb.base)) |ridx| {
                    const rdef = &self.record_defs.items[ridx];
                    if (!rdef.is_flat_c) {
                        self.addError(.invalid_ffi_type, span, "Rust FFI record borrow requires @layout(flat)");
                        return;
                    }
                    _ = self.isFlatCABIScalarOrRecord(span, pb.base, 0);
                    return;
                }
                self.addError(.invalid_ffi_type, span, "Rust FFI path borrow must target a flat Collection or @layout(flat) record");
            },
            .view => |v| {
                if (v.target.* == .opaque_ty) return;
                if (v.target.* == .slice or v.target.* == .collection or v.target.* == .record) {
                    self.validateRustFFIType(span, v.target, is_return);
                    return;
                }
                self.addError(.invalid_ffi_type, span, "Rust FFI view must wrap an opaque handle, C-ABI slice, flat record, or flat Collection");
            },
            else => {
                self.addError(.invalid_ffi_type, span, "unsupported composite type across Rust C-ABI FFI boundary; use scalars, flat structs, slices, collections, or opaque handles");
            },
        }
    }

    fn recordOfType(ty: *const Ty) ?usize {
        return switch (ty.*) {
            .record => |idx| idx,
            .applied => |ap| if (ap.kind == .record) ap.decl_idx else null,
            .collection => |c| c.elem_record,
            .vec => |v| v.elem_record,
            .view => |v| v.target_record orelse recordOfType(v.target),
            .path_borrow => |pb| recordOfType(pb.base),
            else => null,
        };
    }

    fn isHashableEqKey(ty: *const Ty) bool {
        return switch (ty.*) {
            .int, .int_range, .bool, .string, .unit, .type_var, .err => true,
            .record, .adt => true,
            .applied => |ap| blk: {
                if (ap.kind == .opaque_ty) break :blk false;
                for (ap.args) |el| if (!isHashableEqKey(el)) break :blk false;
                break :blk true;
            },
            .option => |inner| isHashableEqKey(inner),
            .result => |res| isHashableEqKey(res.ok) and isHashableEqKey(res.err),
            .tuple => |elems| blk: {
                for (elems) |el| if (!isHashableEqKey(el)) break :blk false;
                break :blk true;
            },
            else => false,
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

    fn recordTypeBitInfo(self: *const Analyzer, ridx: usize, depth: u8) TypeBitInfo {
        if (depth > 8 or ridx >= self.record_defs.items.len) {
            return .{ .bits = 0, .signed = false, .size = 8, .alignment = 8, .packable = false };
        }
        const rdef = &self.record_defs.items[ridx];
        if (!rdef.fields_resolved) {
            return .{ .bits = 0, .signed = false, .size = 8, .alignment = 8, .packable = false };
        }
        if (rdef.fields.len == 0) {
            return .{ .bits = 0, .signed = false, .size = 0, .alignment = 1, .packable = false };
        }
        var cursor: usize = 0;
        var max_align: usize = 1;
        for (rdef.fields) |f| {
            const inner = self.typeBitInfoDepth(f.ty, depth + 1);
            const a = @max(@as(usize, 1), inner.alignment);
            if (a > max_align) max_align = a;
            cursor = layout.alignUp(cursor, a) + inner.size;
        }
        const total = layout.alignUp(cursor, max_align);
        return .{
            .bits = @min(@as(u16, 65535), @as(u16, @intCast(total * 8))),
            .signed = false,
            .size = total,
            .alignment = max_align,
            .packable = false,
        };
    }

    fn typeBitInfo(self: *const Analyzer, ty: *const Ty) TypeBitInfo {
        return self.typeBitInfoDepth(ty, 0);
    }

    fn typeBitInfoDepth(self: *const Analyzer, ty: *const Ty, depth: u8) TypeBitInfo {
        switch (ty.*) {
            .int => |it| {
                const slot = layout.naturalSlot(it.bits);
                return .{ .bits = it.bits, .signed = it.signed, .size = slot.size, .alignment = slot.alignment, .packable = it.bits > 0 and it.bits % 8 != 0 };
            },
            .int_range => |ir| {
                const slot = layout.naturalSlot(ir.synthesized.bits);
                return .{ .bits = ir.synthesized.bits, .signed = ir.synthesized.signed, .size = slot.size, .alignment = slot.alignment, .packable = ir.synthesized.bits > 0 and ir.synthesized.bits % 8 != 0 };
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
                    .packable = false,
                };
            },
            .opaque_ty => return .{ .bits = 64, .signed = false, .size = 8, .alignment = 8, .packable = false },
            .collection, .slice, .string => {
                const slot = layout.naturalSlot(128);
                return .{ .bits = 128, .signed = false, .size = slot.size, .alignment = slot.alignment, .packable = false };
            },
            .record => |ridx| return self.recordTypeBitInfo(ridx, depth),
            .applied => |ap| switch (ap.kind) {
                .record => return self.recordTypeBitInfo(ap.decl_idx, depth),
                .adt => {
                    const aty = Ty{ .adt = ap.decl_idx };
                    return self.typeBitInfoDepth(&aty, depth);
                },
                .opaque_ty => return .{ .bits = 64, .signed = false, .size = 8, .alignment = 8, .packable = false },
            },
            else => return .{ .bits = 64, .signed = false, .size = 8, .alignment = 8, .packable = false },
        }
    }

    fn isHKTActive(self: *const Analyzer, name: []const u8) bool {
        for (self.active_hkt_params.items) |h| {
            if (std.mem.eql(u8, h, name)) return true;
        }
        return false;
    }

    fn resolveBrandForConstraints(self: *Analyzer, cs: []const ResolvedConstraint, subst: *const std.StringHashMapUnmanaged(*const Ty), span: ast.Span) ?[]const u8 {
        if (cs.len == 0) return null;
        const c = cs[0];
        var sub_args = self.alloc.alloc(*const Ty, c.args.len) catch return null;
        for (c.args, 0..) |a, i| {
            sub_args[i] = self.substituteType(a, subst) catch a;
        }
        const w = self.resolveTraitWitness(c.trait_idx, sub_args, c.hkt_arg_names, span, false) orelse return null;
        return switch (w) {
            .concrete => |cw| self.instance_defs.items[cw.inst_idx].name,
            .param => |pidx| std.fmt.allocPrint(self.alloc, "__param_{d}", .{pidx}) catch null,
        };
    }

    fn makeAppliedOrNominal(
        self: *Analyzer,
        kind: @TypeOf(@as(Ty, undefined).applied).AppliedKind,
        idx: usize,
        raw_args: []const *const ast.TypeExpr,
        tparams: []const []const u8,
        cs: []const ResolvedConstraint,
        span: ast.Span,
    ) std.mem.Allocator.Error!*const Ty {
        if (raw_args.len == 0 and tparams.len == 0 and cs.len == 0) {
            return switch (kind) {
                .record => try self.allocTy(.{ .record = idx }),
                .adt => try self.allocTy(.{ .adt = idx }),
                .opaque_ty => try self.allocTy(.{ .opaque_ty = idx }),
            };
        }
        const args = try self.alloc.alloc(*const Ty, raw_args.len);
        var subst: std.StringHashMapUnmanaged(*const Ty) = .empty;
        for (raw_args, 0..) |ra, i| {
            args[i] = try self.resolveType(ra);
            if (i < tparams.len) try subst.put(self.alloc, tparams[i], args[i]);
        }
        const brand = self.resolveBrandForConstraints(cs, &subst, span);
        return try self.allocTy(.{ .applied = .{
            .kind = kind,
            .decl_idx = idx,
            .args = args,
            .brand_inst = brand,
        } });
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

                if (n.path.len == 1 and n.args.len == 1 and self.isHKTActive(head_name)) {
                    const inner = try self.resolveType(n.args[0]);
                    return try self.allocTy(.{ .hkt_app = .{ .ctor = head_name, .arg = inner } });
                }

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
                if (std.mem.eql(u8, head_name, "Vec")) {
                    const elem = if (n.args.len > 0) try self.resolveType(n.args[0]) else try self.allocTy(.err);
                    const ridx_opt = recordOfType(elem);
                    if (ridx_opt) |ri| {
                        self.record_defs.items[ri].used_in_dyn_vec = true;
                    }
                    return try self.allocTy(.{ .vec = .{
                        .elem_record = ridx_opt,
                        .elem_ty = elem,
                    } });
                }
                if (std.mem.eql(u8, head_name, "Map")) {
                    const key_ty = if (n.args.len > 0) try self.resolveType(n.args[0]) else try self.allocTy(.err);
                    const val_ty = if (n.args.len > 1) try self.resolveType(n.args[1]) else try self.allocTy(.err);
                    if (!isHashableEqKey(key_ty)) {
                        self.addError(.type_mismatch, n.span, "Map key type must satisfy deterministic Eq and Hash (floats, views, and mutable handles are not valid keys)");
                    }
                    return try self.allocTy(.{ .map = .{
                        .key_ty = key_ty,
                        .val_ty = val_ty,
                    } });
                }
                if (std.mem.eql(u8, head_name, "Set")) {
                    const elem = if (n.args.len > 0) try self.resolveType(n.args[0]) else try self.allocTy(.err);
                    if (!isHashableEqKey(elem)) {
                        self.addError(.type_mismatch, n.span, "Set element type must satisfy deterministic Eq and Hash (floats, views, and mutable handles are not valid elements)");
                    }
                    return try self.allocTy(.{ .set = .{
                        .elem_ty = elem,
                    } });
                }
                if (std.mem.eql(u8, head_name, "Deque")) {
                    const elem = if (n.args.len > 0) try self.resolveType(n.args[0]) else try self.allocTy(.err);
                    return try self.allocTy(.{ .deque = .{
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

                if (n.path.len >= 2) {
                    const mod_alias = n.path[0].slice(self.source);
                    const tname = n.path[n.path.len - 1].slice(self.source);
                    if (self.resolveImportedModule(self.current_module_id, mod_alias)) |target_mod| {
                        if (self.findRecordInModule(target_mod, tname)) |ridx| {
                            if (!self.record_defs.items[ridx].is_pub and target_mod != self.current_module_id) {
                                self.addError(.visibility_error, n.span, "cannot use private record type from imported module");
                            }
                            const rdef = self.record_defs.items[ridx];
                            return try self.makeAppliedOrNominal(.record, ridx, n.args, rdef.type_params, rdef.constraints, n.span);
                        }
                        if (self.findADTInModule(target_mod, tname)) |aidx| {
                            if (!self.adt_defs.items[aidx].is_pub and target_mod != self.current_module_id) {
                                self.addError(.visibility_error, n.span, "cannot use private type from imported module");
                            }
                            const adef = self.adt_defs.items[aidx];
                            return try self.makeAppliedOrNominal(.adt, aidx, n.args, adef.type_params, adef.constraints, n.span);
                        }
                        if (self.findOpaqueInModule(target_mod, tname)) |oidx| {
                            if (!self.opaque_defs.items[oidx].is_pub and target_mod != self.current_module_id) {
                                self.addError(.visibility_error, n.span, "cannot use private opaque type from imported module");
                            }
                            return try self.allocTy(.{ .opaque_ty = oidx });
                        }
                        if (self.findTypeAliasInModule(target_mod, tname)) |ta| {
                            if (!ta.is_pub and target_mod != self.current_module_id) {
                                self.addError(.visibility_error, n.span, "cannot use private type alias from imported module");
                            }
                            return ta.ty;
                        }
                        self.addError(.unknown_type, n.span, "unknown type name in imported module");
                        return try self.allocTy(.err);
                    }
                    return try self.allocTy(.{ .type_var = head_name });
                }

                if (self.findRecordInModule(self.current_module_id, head_name)) |ridx| {
                    const rdef = self.record_defs.items[ridx];
                    return try self.makeAppliedOrNominal(.record, ridx, n.args, rdef.type_params, rdef.constraints, n.span);
                }
                if (self.findADTInModule(self.current_module_id, head_name)) |aidx| {
                    const adef = self.adt_defs.items[aidx];
                    return try self.makeAppliedOrNominal(.adt, aidx, n.args, adef.type_params, adef.constraints, n.span);
                }
                if (self.findOpaqueInModule(self.current_module_id, head_name)) |oidx| {
                    return try self.allocTy(.{ .opaque_ty = oidx });
                }
                if (self.findTypeAliasInModule(self.current_module_id, head_name)) |ta| {
                    return ta.ty;
                }
                if (self.memberImportTarget(self.current_module_id, head_name)) |target_mod| {
                    if (self.findRecordInModule(target_mod, head_name)) |ridx| {
                        if (!self.record_defs.items[ridx].is_pub and target_mod != self.current_module_id) {
                            self.addError(.visibility_error, n.span, "cannot import private record type");
                        }
                        const rdef = self.record_defs.items[ridx];
                        return try self.makeAppliedOrNominal(.record, ridx, n.args, rdef.type_params, rdef.constraints, n.span);
                    }
                    if (self.findADTInModule(target_mod, head_name)) |aidx| {
                        if (!self.adt_defs.items[aidx].is_pub and target_mod != self.current_module_id) {
                            self.addError(.visibility_error, n.span, "cannot import private type");
                        }
                        const adef = self.adt_defs.items[aidx];
                        return try self.makeAppliedOrNominal(.adt, aidx, n.args, adef.type_params, adef.constraints, n.span);
                    }
                    if (self.findOpaqueInModule(target_mod, head_name)) |oidx| {
                        if (!self.opaque_defs.items[oidx].is_pub and target_mod != self.current_module_id) {
                            self.addError(.visibility_error, n.span, "cannot import private opaque type");
                        }
                        return try self.allocTy(.{ .opaque_ty = oidx });
                    }
                    if (self.findTypeAliasInModule(target_mod, head_name)) |ta| {
                        if (!ta.is_pub and target_mod != self.current_module_id) {
                            self.addError(.visibility_error, n.span, "cannot import private type alias");
                        }
                        return ta.ty;
                    }
                }
                if (self.module_slices.len == 0) {
                    if (self.findRecordIndex(head_name)) |ridx| {
                        const rdef = self.record_defs.items[ridx];
                        return try self.makeAppliedOrNominal(.record, ridx, n.args, rdef.type_params, rdef.constraints, n.span);
                    }
                    if (self.findADTIndex(head_name)) |aidx| {
                        const adef = self.adt_defs.items[aidx];
                        return try self.makeAppliedOrNominal(.adt, aidx, n.args, adef.type_params, adef.constraints, n.span);
                    }
                    if (self.findOpaqueIndex(head_name)) |oidx| {
                        return try self.allocTy(.{ .opaque_ty = oidx });
                    }
                    if (self.type_aliases.get(head_name)) |aliased| {
                        return aliased;
                    }
                }
                // Unknown unqualified type name.
                self.addError(.unknown_type, n.span, "unknown type name");
                return try self.allocTy(.err);
            },
            .type_var => |tv| {
                const name = tv.name.slice(self.source);
                if (self.findTypeAliasInModule(self.current_module_id, name)) |ta| return ta.ty;
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
                    return std.math.negate(inner) catch null;
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
            self.current_module_id = self.moduleIdOfSpan(decl.span);
            switch (decl.kind) {
                .const_decl => |cd| {
                    try self.pushScope();
                    defer self.popScope();

                    const local_name = cd.name.slice(self.source);
                    const cname = try self.canonicalName(self.current_module_id, local_name, false);
                    try self.decl_canonical_names.put(self.alloc, decl.span.start, cname);
                    const expected: ?*const Ty = if (cd.ty) |t| try self.resolveType(t) else null;
                    const res = try self.checkExpr(cd.value, expected);
                    const final_ty = expected orelse try self.finalizeInferredType(cd.value.getSpan(), res);
                    if (expected) |exp| {
                        try self.checkAssignmentValue(decl.span, exp, res);
                    }
                    try self.const_types.put(self.alloc, cname, final_ty);
                    const ce = ConstEntry{
                        .name = cname,
                        .local_name = local_name,
                        .module_id = self.current_module_id,
                        .is_pub = decl.is_pub,
                        .ty = final_ty,
                        .range = res.range,
                    };
                    try self.const_map.put(self.alloc, cname, ce);
                    try self.const_list.append(self.alloc, ce);
                },
                .extern_decl => |ex| {
                    for (ex.fns) |ef| {
                        const ename = ef.name.slice(self.source);
                        if (self.findFnIndex(ename)) |fidx| {
                            const fsig = self.fn_sigs.items[fidx];
                            try self.checked_functions.append(self.alloc, .{
                                .name = fsig.name,
                                .span = ef.span,
                                .type_params = fsig.type_params,
                                .param_types = fsig.params,
                                .ret_type = fsig.ret,
                                .reads = &.{},
                                .writes = &.{},
                                .preserves = &.{},
                                .target_record = null,
                                .has_extern_abi = true,
                                .perm_trace = &.{},
                                .disjoint_certs = &.{},
                                .decreases_certs = &.{},
                                .returned_origin = null,
                            });
                        }
                    }
                },
                else => {},
            }
        }

        for (self.module.decls) |decl| {
            self.current_module_id = self.moduleIdOfSpan(decl.span);
            switch (decl.kind) {
                .fn_decl => |fd| {
                    if (fd.has_body) {
                        try self.checkFunction(decl.span, decl.kind);
                    } else {
                        const local_name = fd.name.slice(self.source);
                        const fsig_idx = self.findFnInModule(self.current_module_id, local_name) orelse self.findFnIndex(local_name) orelse continue;
                        const fsig = self.fn_sigs.items[fsig_idx];
                        try self.checked_functions.append(self.alloc, .{
                            .name = fsig.name,
                            .span = decl.span,
                            .type_params = fsig.type_params,
                            .hkt_params = fsig.hkt_params,
                            .constraint_count = fsig.constraints.len,
                            .param_types = fsig.params,
                            .ret_type = fsig.ret,
                            .reads = &.{},
                            .writes = &.{},
                            .preserves = &.{},
                            .target_record = fsig.target_record,
                            .has_extern_abi = true,
                            .rust_sym = fsig.rust_sym,
                            .perm_trace = &.{},
                            .disjoint_certs = &.{},
                            .decreases_certs = &.{},
                            .returned_origin = null,
                        });
                    }
                },
                .trait_decl => |tr| {
                    try self.checkTraitLawsWellTyped(decl.span, tr);
                },
                .instance_decl => |inst| {
                    try self.checkInstanceBodies(decl.span, inst);
                },
                else => {},
            }
        }
    }

    fn checkFunction(self: *Analyzer, span: ast.Span, fd: ast.Decl.Kind) std.mem.Allocator.Error!void {
        const f = fd.fn_decl;
        const local_name = f.name.slice(self.source);
        const fsig_idx = self.findFnInModule(self.current_module_id, local_name) orelse self.findFnIndex(local_name) orelse return;
        const fname = self.fn_sigs.items[fsig_idx].name;
        var fsig = &self.fn_sigs.items[fsig_idx];

        const prev_constraints = self.active_constraints;
        const hkt_mark = self.active_hkt_params.items.len;
        self.active_constraints = fsig.constraints;
        for (fsig.hkt_params) |hp| try self.active_hkt_params.append(self.alloc, hp);
        defer {
            self.active_constraints = prev_constraints;
            self.active_hkt_params.shrinkRetainingCapacity(hkt_mark);
        }

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
        const prev_return_field = self.inferred_return_field;
        self.current_accesses = &accesses;
        self.current_perm_trace = &perm_trace;
        self.current_disjoint_certs = &disjoint_certs;
        self.current_decreases_certs = &decreases_certs;
        self.current_fn_name = fname;
        self.current_fn_params = fn_param_names;
        self.current_fn_decreases = f.decreases;
        self.current_fn_ret = fsig.ret;
        self.inferred_return_origin = fsig.returned_origin;
        self.inferred_return_field = .pending;
        self.field_ranges.clearRetainingCapacity();
        defer {
            self.field_ranges.clearRetainingCapacity();
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
            self.inferred_return_field = prev_return_field;
        }

        const body_res = try self.checkBlock(&f.body, fsig.ret, f.ret != null);
        if (f.ret != null and !fsig.ret.eql(.unit)) {
            if (f.body.tail != null or f.body.stmts.len == 0) {
                const tail_op: ?ast.BinaryOp = if (f.body.tail != null and f.body.tail.?.* == .binary) f.body.tail.?.binary.op else null;
                try self.checkAssignmentValueWithOp(f.body.span, fsig.ret, body_res, tail_op);
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
        if (self.inferred_return_field == .precise and
            self.inferred_return_field.precise.param_idx == fsig.returned_origin)
        {
            fsig.returned_field = self.inferred_return_field.precise;
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
            .hkt_params = fsig.hkt_params,
            .constraint_count = fsig.constraints.len,
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
                    const init_op: ?ast.BinaryOp = if (ls.value.* == .binary) ls.value.binary.op else null;
                    try self.checkAssignmentValueWithOp(ls.span, exp, val_res, init_op);
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
                } else if ((final_ty.* == .slice or final_ty.* == .collection) and self.scopes.items.len > scopes_before and ls.pattern.* == .ident) {
                    if (self.extractDynVecBorrowRoot(ls.value)) |rn| {
                        try self.attachSharedBorrowBinding(&self.scopes.items[self.scopes.items.len - 1], rn, ls.span);
                    }
                }
            },
            .use_stmt => |us| {
                const rhs_res = try self.checkExpr(us.expr, null);
                for (us.patterns) |pat| {
                    try self.bindPattern(pat, rhs_res.ty, rhs_res.range, false);
                }
            },
            .assign_stmt => |asg| {
                const hinted_raw = self.peekWriteTargetType(asg.target);
                const hinted_ty: ?*const Ty = if (hinted_raw) |ht|
                    if (ht.* == .view and ht.view.mode == .exclusive and ht.view.target.* != .slice and ht.view.target.* != .collection)
                        ht.view.target
                    else
                        ht
                else
                    null;
                const rhs = try self.checkExpr(asg.value, hinted_ty);
                const rhs_res = if (asg.op == .assign and hinted_ty != null and hinted_ty.?.isInteger() != null)
                    try self.readIntegerOperand(asg.value, rhs)
                else
                    rhs;
                const target_info = try self.checkWriteTarget(asg.target, asg.span);
                try self.expr_types.put(self.alloc, asg.target, target_info.ty);
                const is_view_rebind = blk: {
                    if (asg.op == .assign and asg.target.* == .ident and target_info.ty.* == .view and rhs_res.ty.* == .view) {
                        if (self.lookupVar(asg.target.ident.slice(self.source))) |vb| {
                            break :blk vb.mutable and vb.view_id == null and target_info.ty.eql(rhs_res.ty.*);
                        }
                    }
                    break :blk false;
                };
                const write_val_ty: *const Ty = if (!is_view_rebind and target_info.ty.* == .view and
                    target_info.ty.view.mode == .exclusive and
                    target_info.ty.view.target.* != .slice and
                    target_info.ty.view.target.* != .collection)
                    target_info.ty.view.target
                else
                    target_info.ty;
                const write_val_range: ?IntRange = if (write_val_ty != target_info.ty) write_val_ty.rangeOf() else target_info.range;
                var post_range: ?IntRange = null;
                if (asg.op == .assign) {
                    try self.checkAssignmentValueWithOp(asg.span, write_val_ty, rhs_res, null);
                    post_range = rhs_res.range orelse write_val_ty.rangeOf();
                } else {
                    const lhs_res = ExprResult{ .ty = write_val_ty, .range = write_val_range };
                    const op_bin: ast.BinaryOp = switch (asg.op) {
                        .add_assign => .add,
                        .sub_assign => .sub,
                        .mul_assign => .mul,
                        .div_assign => .div,
                        .rem_assign => .rem,
                        .assign => .add,
                    };
                    if (isTraitDispatchableScalarTarget(write_val_ty)) {
                        if (try self.resolveNumericOpTrait(null, asg.span, op_bin, write_val_ty)) |ctr| {
                            if (!write_val_ty.eql(rhs_res.ty.*)) {
                                self.addError(.type_mismatch, asg.span, "compound assignment operand type mismatch");
                            }
                            try self.assign_trait_resolutions.put(self.alloc, stmt, ctr);
                        }
                    } else {
                        const combined = try self.combineBinary(asg.span, op_bin, lhs_res, rhs_res, write_val_ty);
                        try self.checkAssignmentValueWithOp(asg.span, write_val_ty, combined, op_bin);
                        post_range = combined.range orelse write_val_ty.rangeOf();
                    }
                }
                if (asg.target.* == .ident) {
                    const rname = asg.target.ident.slice(self.source);
                    self.invalidateRootFieldRanges(rname);
                    if (self.lookupVar(rname)) |vb| {
                        if (vb.view_root) |vr| {
                            self.invalidateRootFieldRanges(vr);
                        }
                    }
                } else if (self.extractPureFieldPath(asg.target)) |fp| {
                    if (post_range) |pr| {
                        try self.setFieldRange(fp.root, fp.field, pr);
                    } else {
                        self.removeFieldRange(fp.root, fp.field);
                    }
                }
            },
            .return_stmt => |rs| {
                if (rs.value) |v| {
                    const rv = try self.checkExpr(v, self.current_fn_ret);
                    if (self.current_fn_ret) |ret_ty| {
                        if (!ret_ty.eql(.unit)) {
                            const ret_op: ?ast.BinaryOp = if (v.* == .binary) v.binary.op else null;
                            try self.checkAssignmentValueWithOp(rs.span, ret_ty, rv, ret_op);
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
                const saved_field_ranges = try self.alloc.dupe(FieldRangeEntry, self.field_ranges.items);
                defer {
                    for (0..saved_ranges.len) |si| {
                        if (si < self.scopes.items.len) self.scopes.items[si].range = saved_ranges[si];
                    }
                    self.field_ranges.clearRetainingCapacity();
                    self.field_ranges.appendSlice(self.alloc, saved_field_ranges) catch {};
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
                    .vec => |v| v.elem_ty,
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
                const vname = if (ctor.path.len > 0) ctor.path[ctor.path.len - 1].slice(self.source) else "";
                if (ty.* == .option) {
                    if (std.mem.eql(u8, vname, "Some") and ctor.args.len >= 1) {
                        try self.bindPattern(ctor.args[0].pattern, ty.option, ty.option.rangeOf(), default_mut);
                    }
                    return;
                }
                if (ty.* == .result) {
                    if (std.mem.eql(u8, vname, "Ok") and ctor.args.len >= 1) {
                        try self.bindPattern(ctor.args[0].pattern, ty.result.ok, ty.result.ok.rangeOf(), default_mut);
                    } else if (std.mem.eql(u8, vname, "Err") and ctor.args.len >= 1) {
                        try self.bindPattern(ctor.args[0].pattern, ty.result.err, ty.result.err.rangeOf(), default_mut);
                    }
                    return;
                }
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
                const is_excl_view_target = vb.ty.* == .view and vb.ty.view.mode == .exclusive and
                    vb.ty.view.target.* != .slice and vb.ty.view.target.* != .collection;
                if (!vb.mutable and !is_excl_view_target) {
                    self.addError(.mutability_error, sp, "cannot assign to immutable binding; mark with 'mut'");
                }
                if (is_excl_view_target and (vb.view_id != null or vb.view_root != null)) {
                    try self.recordAccess(
                        vb.view_root orelse name,
                        vb.view_record_idx orelse recordOfType(vb.ty.view.target),
                        vb.view_field_idx,
                        true,
                        stmt_span,
                        vb.view_index_key,
                        vb.view_id,
                    );
                } else if (self.active_fork_start) |fstart| {
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
                const narrowed_rng = if (fld.target.* == .ident)
                    self.lookupFieldRange(fld.target.ident.slice(self.source), fname)
                else
                    null;
                return .{ .ty = cf.ty, .range = narrowed_rng orelse cf.ty.rangeOf() };
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
                    .vec => |v| v.elem_ty,
                    .view => |v| switch (v.target.*) {
                        .slice => |sl| sl.elem,
                        .collection => |c| c.elem_ty,
                        .vec => |vc| vc.elem_ty,
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
                        } else if (vb.ty.* == .vec and !vb.mutable) {
                            self.addError(.mutability_error, ix.target.getSpan(), "cannot write element of immutable Vec; mark binding 'mut'");
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

    const f32_exact_int_limit: i128 = 16_777_216;
    const f64_exact_int_limit: i128 = 9_007_199_254_740_992;

    fn intRangeFitsFloat(rng: IntRange, is_f64: bool) bool {
        return switch (rng) {
            .bounded => |b| blk: {
                const lim = if (is_f64) f64_exact_int_limit else f32_exact_int_limit;
                break :blk b.lo >= -lim and b.hi <= lim;
            },
            .wide => |w| w.bits <= (if (is_f64) @as(u16, 53) else @as(u16, 24)),
        };
    }

    fn canWidenNumericLossless(src_ty: *const Ty, src_range: ?IntRange, dst_ty: *const Ty) bool {
        switch (dst_ty.*) {
            .int => |it| {
                const eff = src_range orelse src_ty.rangeOf() orelse return false;
                return eff.fitsType(it);
            },
            .int_range => |ir| {
                const eff = src_range orelse src_ty.rangeOf() orelse return false;
                return ir.range.containsRange(eff);
            },
            .f32 => {
                if (src_ty.* == .f32) return true;
                const eff = src_range orelse src_ty.rangeOf() orelse return false;
                return intRangeFitsFloat(eff, false);
            },
            .f64 => {
                if (src_ty.* == .f32 or src_ty.* == .f64) return true;
                const eff = src_range orelse src_ty.rangeOf() orelse return false;
                return intRangeFitsFloat(eff, true);
            },
            else => return false,
        }
    }

    fn joinLosslessScalarTy(self: *Analyzer, a: *const Ty, b: *const Ty) std.mem.Allocator.Error!?*const Ty {
        if (a.eql(b.*)) return a;
        if (a.isInteger() != null and b.isInteger() != null) {
            const r1 = a.rangeOf() orelse return null;
            const r2 = b.rangeOf() orelse return null;
            const jr = r1.join(r2);
            const it = int_range.inferIntegerType(jr) orelse return null;
            return try self.allocTy(.{ .int = it });
        }
        if ((a.* == .f64 and b.* == .f32) or (a.* == .f32 and b.* == .f64)) {
            return try self.allocTy(.f64);
        }
        if (a.* == .f32 or a.* == .f64) {
            if (b.isInteger() != null) {
                const r = b.rangeOf() orelse return null;
                if (a.* == .f32 and intRangeFitsFloat(r, false)) return a;
                if (intRangeFitsFloat(r, true)) return try self.allocTy(.f64);
            }
            return null;
        }
        if (b.* == .f32 or b.* == .f64) {
            if (a.isInteger() != null) {
                const r = a.rangeOf() orelse return null;
                if (b.* == .f32 and intRangeFitsFloat(r, false)) return b;
                if (intRangeFitsFloat(r, true)) return try self.allocTy(.f64);
            }
            return null;
        }
        return null;
    }

    fn formatRangeDesc(self: *Analyzer, ty: *const Ty, rng_opt: ?IntRange) []const u8 {
        if (rng_opt) |rng| {
            switch (rng) {
                .bounded => |b| {
                    if (int_range.inferIntegerType(rng)) |synth| {
                        return std.fmt.allocPrint(self.alloc, "{d}..={d} ({c}{d})", .{
                            b.lo,
                            b.hi,
                            if (synth.signed) @as(u8, 'i') else @as(u8, 'u'),
                            synth.bits,
                        }) catch "integer range";
                    }
                    return std.fmt.allocPrint(self.alloc, "{d}..={d}", .{ b.lo, b.hi }) catch "integer range";
                },
                .wide => |w| {
                    return std.fmt.allocPrint(self.alloc, "{c}{d}", .{
                        if (w.signed) @as(u8, 'i') else @as(u8, 'u'),
                        w.bits,
                    }) catch "wide integer";
                },
            }
        }
        if (ty.isInteger()) |it| {
            return std.fmt.allocPrint(self.alloc, "{c}{d}", .{
                if (it.signed) @as(u8, 'i') else @as(u8, 'u'),
                it.bits,
            }) catch "integer";
        }
        return "target type";
    }

    fn reportOverflowDiagnostic(
        self: *Analyzer,
        span: ast.Span,
        op_hint: ?ast.BinaryOp,
        src_ty: *const Ty,
        src_range: ?IntRange,
        dst_ty: *const Ty,
    ) void {
        const src_desc = self.formatRangeDesc(src_ty, src_range orelse src_ty.rangeOf());
        const dst_desc = self.formatRangeDesc(dst_ty, dst_ty.rangeOf());
        const op_advice: []const u8 = if (op_hint) |op| switch (op) {
            .add => "use '+|' (saturating) or '+%' (wrapping)",
            .sub => "use '-|' (saturating) or '-%' (wrapping)",
            .mul => "use '*|' (saturating) or '*%' (wrapping)",
            else => "use saturating '+|'/'-|'/'*|' or wrapping '+%'/'-%'/'*%'",
        } else "use saturating '+|'/'-|'/'*|' or wrapping '+%'/'-%'/'*%'";
        const msg = std.fmt.allocPrint(
            self.alloc,
            "potential integer overflow: expression range {s} exceeds target {s}; help: {s}, widen target type, or add a range guard",
            .{ src_desc, dst_desc, op_advice },
        ) catch "potential integer overflow: expression range exceeds target integer type";
        self.addError(.potential_overflow, span, msg);
    }

    fn checkAssignmentValue(self: *Analyzer, span: ast.Span, target: *const Ty, val: ExprResult) std.mem.Allocator.Error!void {
        try self.checkAssignmentValueWithOp(span, target, val, null);
    }

    fn checkAssignmentValueWithOp(
        self: *Analyzer,
        span: ast.Span,
        target: *const Ty,
        val: ExprResult,
        op_hint: ?ast.BinaryOp,
    ) std.mem.Allocator.Error!void {
        if (target.* == .err) return;
        if (val.ty.* == .err and val.unsized_literal == null and val.range == null) return;

        // Check unsized integer literal fit directly against target integer / IntRange / float / scalar View type.
        if (val.unsized_literal) |lit| {
            const lit_target: *const Ty = if (target.* == .view) target.view.target else target;
            switch (lit_target.*) {
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
                .f32, .f64 => {
                    if (val.range) |lr| {
                        if (!intRangeFitsFloat(lr, lit_target.* == .f64)) {
                            self.addError(.literal_out_of_range, span, "integer literal exceeds exact float precision; use explicit 'as'");
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

        // Check lossless numeric widening & integer overflow safety!
        switch (target.*) {
            .int, .int_range => {
                if (val.ty.isInteger() != null or val.ty.* == .int_range) {
                    if (!canWidenNumericLossless(val.ty, val.range, target)) {
                        self.reportOverflowDiagnostic(span, op_hint, val.ty, val.range, target);
                    }
                    return;
                }
            },
            .f32, .f64 => {
                if (val.ty.* == .f32 or val.ty.* == .f64 or val.ty.isInteger() != null or val.ty.* == .int_range) {
                    if (!canWidenNumericLossless(val.ty, val.range, target)) {
                        self.addError(.type_mismatch, span, "cannot implicitly widen float or wide integer without precision loss; use explicit 'as'");
                    }
                    return;
                }
            },
            else => {},
        }

        if (target.* == .path_borrow) {
            if (target.path_borrow.base.eql(val.ty.*)) return;
            if (target.path_borrow.base.* == .collection and val.ty.* == .vec and
                target.path_borrow.base.collection.elem_ty.eql(val.ty.vec.elem_ty.*))
            {
                return;
            }
        }
        if (val.ty.* == .path_borrow) {
            if (val.ty.path_borrow.base.eql(target.*)) return;
        }
        if (target.* == .collection and val.ty.* == .vec) {
            if (target.collection.elem_ty.eql(val.ty.vec.elem_ty.*)) return;
        }
        if (target.* == .view) {
            const inner_ok = switch (val.ty.*) {
                .view => |vv| blk: {
                    if (target.view.mode == .exclusive and vv.mode == .shared) {
                        self.addError(.borrow_conflict, span, "cannot coerce shared View to Exclusive View");
                    }
                    if (target.view.target.* == .slice and vv.target.* == .slice) {
                        break :blk target.view.target.slice.elem.eql(vv.target.slice.elem.*);
                    }
                    if (target.view.target.* == .collection and vv.target.* == .vec) {
                        break :blk target.view.target.collection.elem_ty.eql(vv.target.vec.elem_ty.*);
                    }
                    break :blk target.view.target.eql(vv.target.*);
                },
                .path_borrow => |pb| blk: {
                    if (target.view.mode == .exclusive and pb.mode != null and pb.mode.? == .shared) {
                        self.addError(.borrow_conflict, span, "cannot coerce shared path borrow to Exclusive View");
                    }
                    break :blk target.view.target.eql(pb.base.*);
                },
                .vec => |vc| blk: {
                    if (target.view.target.* == .collection) {
                        break :blk target.view.target.collection.elem_ty.eql(vc.elem_ty.*);
                    }
                    if (target.view.target.* == .slice) {
                        break :blk target.view.target.slice.elem.eql(vc.elem_ty.*);
                    }
                    break :blk target.view.target.eql(val.ty.*);
                },
                .slice => |sl| blk: {
                    if (target.view.target.* != .slice) break :blk false;
                    if (target.view.mode == .exclusive and !sl.mutable) {
                        self.addError(.mutability_error, span, "cannot coerce immutable slice to Exclusive View");
                    }
                    break :blk target.view.target.slice.elem.eql(sl.elem.*);
                },
                else => target.view.target.eql(val.ty.*),
            };
            if (inner_ok) return;
        }
        if (target.* == .slice and val.ty.* == .vec) {
            if (!target.slice.mutable and target.slice.elem.eql(val.ty.vec.elem_ty.*)) return;
        }
        if (target.* == .slice and val.ty.* == .slice) {
            if (target.slice.mutable and !val.ty.slice.mutable) {
                self.addError(.mutability_error, span, "cannot pass immutable slice where mutable '[mut T]' is expected");
                return;
            }
            if (target.slice.elem.eql(val.ty.slice.elem.*)) return;
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
        if (target.* == .applied and val.ty.* == .applied) {
            const ta = target.applied;
            const va = val.ty.applied;
            if (ta.kind == va.kind and ta.decl_idx == va.decl_idx and ta.brand_inst != null and va.brand_inst != null and
                !std.mem.eql(u8, ta.brand_inst.?, va.brand_inst.?))
            {
                self.addError(.type_mismatch, span, "branded container instance mismatch: cannot mix values created with different instances");
                return;
            }
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
                const rng: ?IntRange = if (parsed.value <= @as(u128, @intCast(std.math.maxInt(i128))))
                    IntRange.singleton(@intCast(parsed.value))
                else
                    null;
                if (expected != null and (expected.?.* == .f32 or expected.?.* == .f64)) {
                    if (rng == null or !intRangeFitsFloat(rng.?, expected.?.* == .f64)) {
                        self.addError(.literal_out_of_range, sp, "integer literal exceeds exact float precision; use explicit 'as'");
                    }
                    return .{
                        .ty = expected.?,
                        .range = rng,
                        .unsized_literal = .{ .negative = false, .mag = parsed.value },
                    };
                }
                if (expected != null and isTraitDispatchableScalarTarget(expected.?)) {
                    if (try self.resolveNumeralFromInt(expr, sp, parsed.value, false, expected.?)) |res_ty| {
                        return .{ .ty = res_ty, .range = null };
                    }
                }
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
                            try self.recordBindingRead(sp, vb);
                        }
                    }
                    // Implicit affine consumption if value is non-copyable (and not explicitly borrowed via call/field).
                    return .{ .ty = vb.ty, .range = vb.range };
                }
                if (self.findConstInModule(self.current_module_id, name)) |ce| {
                    try self.resolved_idents.put(self.alloc, expr, ce.name);
                    return .{ .ty = ce.ty, .range = ce.range };
                }
                if (self.findFnInModule(self.current_module_id, name)) |fidx| {
                    const fs = self.fn_sigs.items[fidx];
                    try self.resolved_idents.put(self.alloc, expr, fs.name);
                    return .{ .ty = try self.allocTy(.{ .fn_ty = .{ .params = fs.params, .ret = fs.ret } }), .range = null };
                }
                if (self.memberImportTarget(self.current_module_id, name)) |target_mod| {
                    if (self.findConstInModule(target_mod, name)) |ce| {
                        if (!ce.is_pub and target_mod != self.current_module_id) {
                            self.addError(.visibility_error, sp, "cannot access private constant from imported module");
                        }
                        try self.resolved_idents.put(self.alloc, expr, ce.name);
                        return .{ .ty = ce.ty, .range = ce.range };
                    }
                    if (self.findFnInModule(target_mod, name)) |fidx| {
                        const fs = self.fn_sigs.items[fidx];
                        if (!fs.is_pub and target_mod != self.current_module_id) {
                            self.addError(.visibility_error, sp, "cannot access private function from imported module");
                        }
                        try self.resolved_idents.put(self.alloc, expr, fs.name);
                        return .{ .ty = try self.allocTy(.{ .fn_ty = .{ .params = fs.params, .ret = fs.ret } }), .range = null };
                    }
                }
                if (self.module_slices.len == 0) {
                    if (self.const_map.get(name)) |ce| {
                        return .{ .ty = ce.ty, .range = ce.range };
                    }
                    if (self.findFnIndex(name)) |fidx| {
                        const fs = self.fn_sigs.items[fidx];
                        return .{ .ty = try self.allocTy(.{ .fn_ty = .{ .params = fs.params, .ret = fs.ret } }), .range = null };
                    }
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
                if (self.findADTInModule(self.current_module_id, name)) |aidx| {
                    return .{ .ty = try self.allocTy(.{ .adt = aidx }), .range = null };
                }
                if (self.memberImportTarget(self.current_module_id, name)) |target_mod| {
                    if (self.findADTInModule(target_mod, name)) |aidx| {
                        return .{ .ty = try self.allocTy(.{ .adt = aidx }), .range = null };
                    }
                }
                if (self.module_slices.len == 0) {
                    if (self.findADTIndex(name)) |aidx| {
                        return .{ .ty = try self.allocTy(.{ .adt = aidx }), .range = null };
                    }
                }
                return .{ .ty = expected orelse try self.allocTy(.{ .type_var = name }), .range = null };
            },
            .unary => |u| {
                if (u.op == .neg and u.operand.* == .int_lit) {
                    const parsed = int_range.parseIntLiteral(u.operand.int_lit.slice(self.source)) orelse {
                        self.addError(.literal_out_of_range, u.span, "negated integer literal out of range");
                        return .{ .ty = try self.allocTy(.err), .range = null };
                    };
                    const neg_rng: ?IntRange = if (parsed.value == @as(u128, 1) << 127)
                        IntRange.singleton(std.math.minInt(i128))
                    else if (parsed.value <= @as(u128, @intCast(std.math.maxInt(i128))))
                        IntRange.singleton(-@as(i128, @intCast(parsed.value)))
                    else
                        null;
                    if (expected != null and (expected.?.* == .f32 or expected.?.* == .f64)) {
                        if (neg_rng == null or !intRangeFitsFloat(neg_rng.?, expected.?.* == .f64)) {
                            self.addError(.literal_out_of_range, u.span, "negated integer literal exceeds exact float precision; use explicit 'as'");
                        }
                        return .{
                            .ty = expected.?,
                            .range = neg_rng,
                            .unsized_literal = .{ .negative = true, .mag = parsed.value },
                        };
                    }
                    if (expected != null and isTraitDispatchableScalarTarget(expected.?)) {
                        if (try self.resolveNumeralFromInt(expr, u.span, parsed.value, true, expected.?)) |res_ty| {
                            return .{ .ty = res_ty, .range = null };
                        }
                    }
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
                    if (isTraitDispatchableScalarTarget(op_res.ty)) {
                        if (try self.resolveNumericTraitByName(expr, u.span, "Ring", "neg", op_res.ty)) |_| {
                            return .{ .ty = op_res.ty, .range = null };
                        }
                    }
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
                const l_lit = isNumericLiteralExpr(b.left);
                const r_lit = isNumericLiteralExpr(b.right);
                var lr: ExprResult = undefined;
                var rr: ExprResult = undefined;
                if (l_lit and !r_lit) {
                    rr = try self.checkExpr(b.right, null);
                    const l_hint: ?*const Ty = if (rr.ty.* != .int_range and rr.ty.* != .err) rr.ty else expected;
                    lr = try self.checkExpr(b.left, l_hint);
                } else {
                    const l_exp: ?*const Ty = switch (b.op) {
                        .add_sat, .sub_sat, .mul_sat, .add_wrap, .sub_wrap, .mul_wrap => expected,
                        else => null,
                    };
                    lr = try self.checkExpr(b.left, l_exp);
                    const r_hint: ?*const Ty = if (r_lit and lr.ty.* != .int_range and lr.ty.* != .err) lr.ty else null;
                    rr = try self.checkExpr(b.right, r_hint);
                }
                switch (b.op) {
                    .eq, .ne, .lt, .le, .gt, .ge, .range, .range_eq, .sub_sat => {
                        const left = try self.readIntegerOperand(b.left, lr);
                        const right = try self.readIntegerOperand(b.right, rr);
                        return try self.combineBinary(b.span, b.op, left, right, expected);
                    },
                    else => {},
                }
                if ((b.op == .add or b.op == .sub or b.op == .mul or b.op == .div) and isTraitDispatchableScalarTarget(lr.ty)) {
                    if (!lr.ty.eql(rr.ty.*)) {
                        self.addError(.type_mismatch, b.span, "binary operator operand types do not match");
                    }
                    if (try self.resolveNumericOpTrait(expr, b.span, b.op, lr.ty)) |_| {
                        return .{ .ty = lr.ty, .range = null };
                    }
                }
                if ((b.op == .eq or b.op == .ne) and isTraitDispatchableScalarTarget(lr.ty)) {
                    if (!lr.ty.eql(rr.ty.*)) {
                        self.addError(.type_mismatch, b.span, "equality operand types do not match");
                    }
                    if (self.resolveVisibleTraitIndex("Eq", b.span)) |eq_tidx| {
                        if (self.resolveTraitWitness(eq_tidx, &.{lr.ty}, &.{null}, b.span, false)) |w| {
                            try self.call_trait_resolutions.put(self.alloc, expr, .{
                                .kind = .{ .trait_method = .{ .method_name = "eq", .witness = w } },
                                .witnesses = &.{},
                                .type_args = &.{},
                            });
                        }
                    }
                    return .{ .ty = try self.allocTy(.bool), .range = null };
                }
                return try self.combineBinary(b.span, b.op, lr, rr, expected);
            },
            .cast => |c| {
                const target_ty = try self.resolveType(c.ty);
                const inner = try self.checkExpr(c.expr, target_ty);
                const is_explicit_float_conv =
                    ((target_ty.* == .f32 or target_ty.* == .f64) and
                        (inner.ty.isInteger() != null or inner.ty.* == .f32 or inner.ty.* == .f64)) or
                    (target_ty.isInteger() != null and (inner.ty.* == .f32 or inner.ty.* == .f64));
                if (!is_explicit_float_conv) {
                    try self.checkAssignmentValue(c.span, target_ty, inner);
                }
                return .{
                    .ty = target_ty,
                    .range = if (target_ty.isInteger() != null) (inner.range orelse target_ty.rangeOf()) else null,
                };
            },
            .call => |call_expr| {
                return try self.checkCall(expr, call_expr.span, call_expr.callee, call_expr.args, null, null, expected);
            },
            .field => |fld| {
                const fname = fld.name.slice(self.source);
                // Module-qualified member access: `math.SCALE`, `math.clamp`, `v2.Status.Idle`, `v2.Idle`.
                if (fld.target.* == .ident and self.lookupVar(fld.target.ident.slice(self.source)) == null) {
                    const mod_alias = fld.target.ident.slice(self.source);
                    if (self.resolveImportedModule(self.current_module_id, mod_alias)) |target_mod| {
                        if (self.findConstInModule(target_mod, fname)) |ce| {
                            if (!ce.is_pub and target_mod != self.current_module_id) {
                                self.addError(.visibility_error, fld.name, "constant is private in imported module");
                            }
                            try self.resolved_idents.put(self.alloc, expr, ce.name);
                            return .{ .ty = ce.ty, .range = ce.range };
                        }
                        if (self.findFnInModule(target_mod, fname)) |fidx| {
                            const fs = self.fn_sigs.items[fidx];
                            if (!fs.is_pub and target_mod != self.current_module_id) {
                                self.addError(.visibility_error, fld.name, "function is private in imported module");
                            }
                            try self.resolved_idents.put(self.alloc, expr, fs.name);
                            return .{ .ty = try self.allocTy(.{ .fn_ty = .{ .params = fs.params, .ret = fs.ret } }), .range = null };
                        }
                        if (self.findADTInModule(target_mod, fname)) |aidx| {
                            if (!self.adt_defs.items[aidx].is_pub and target_mod != self.current_module_id) {
                                self.addError(.visibility_error, fld.name, "type is private in imported module");
                            }
                            return .{ .ty = try self.allocTy(.{ .adt = aidx }), .range = null };
                        }
                        for (self.adt_defs.items, 0..) |adt_def, aidx| {
                            if (adt_def.module_id != target_mod) continue;
                            for (adt_def.variants) |v| {
                                if (std.mem.eql(u8, v.name, fname)) {
                                    if (!adt_def.is_pub and target_mod != self.current_module_id) {
                                        self.addError(.visibility_error, fld.name, "type variant is private in imported module");
                                    }
                                    return .{ .ty = try self.allocTy(.{ .adt = aidx }), .range = null };
                                }
                            }
                        }
                        self.addError(.unknown_ident, fld.name, "unknown symbol in imported module");
                        return .{ .ty = try self.allocTy(.err), .range = null };
                    }
                }
                if (fld.target.* == .field and fld.target.field.target.* == .ident and
                    self.lookupVar(fld.target.field.target.ident.slice(self.source)) == null)
                {
                    const mod_alias = fld.target.field.target.ident.slice(self.source);
                    const adt_name = fld.target.field.name.slice(self.source);
                    if (self.resolveImportedModule(self.current_module_id, mod_alias)) |target_mod| {
                        if (self.findADTInModule(target_mod, adt_name)) |aidx| {
                            if (!self.adt_defs.items[aidx].is_pub and target_mod != self.current_module_id) {
                                self.addError(.visibility_error, fld.target.field.name, "ADT type is private in imported module");
                            }
                            return .{ .ty = try self.allocTy(.{ .adt = aidx }), .range = null };
                        }
                    }
                }
                if (fld.target.* == .upper_ident) {
                    const adt_name = fld.target.upper_ident.slice(self.source);
                    if (self.resolveVisibleADTIndex(adt_name, fld.target.upper_ident)) |aidx| {
                        return .{ .ty = try self.allocTy(.{ .adt = aidx }), .range = null };
                    }
                }

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
                if (std.mem.eql(u8, fname, "len")) {
                    const is_len_container = switch (base.ty.*) {
                        .slice, .collection, .vec, .map, .set, .deque, .string => true,
                        .view => |v| v.target.* == .slice or v.target.* == .collection or v.target.* == .vec or v.target.* == .map or v.target.* == .set or v.target.* == .deque or v.target.* == .string,
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
                        const rdef = self.record_defs.items[ridx];
                        const cf = rdef.fields[fidx];
                        var field_ty = cf.ty;
                        if (base.ty.* == .applied and rdef.type_params.len > 0) {
                            var subst: std.StringHashMapUnmanaged(*const Ty) = .empty;
                            for (rdef.type_params, 0..) |tp, ti| {
                                if (ti < base.ty.applied.args.len) try subst.put(self.alloc, tp, base.ty.applied.args[ti]);
                            }
                            field_ty = try self.substituteType(field_ty, &subst);
                        }
                        if (base.ty.* == .collection) {
                            return .{
                                .ty = try self.allocTy(.{ .slice = .{ .mutable = false, .elem = field_ty } }),
                                .range = null,
                            };
                        }
                        return .{ .ty = field_ty, .range = field_ty.rangeOf() };
                    }
                    self.addError(.unknown_ident, fld.name, "unknown field on record");
                }
                const tup_elems: ?[]const *const Ty = switch (base.ty.*) {
                    .tuple => |ts| ts,
                    .view => |v| if (v.target.* == .tuple) v.target.tuple else null,
                    else => null,
                };
                if (tup_elems) |ts| {
                    if (std.fmt.parseInt(usize, fname, 10) catch null) |tidx| {
                        if (tidx < ts.len) {
                            return .{ .ty = ts[tidx], .range = ts[tidx].rangeOf() };
                        }
                        self.addError(.unknown_ident, fld.name, "tuple index out of bounds");
                        return .{ .ty = try self.allocTy(.err), .range = null };
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
                        .vec => |v| v.elem_ty,
                        .view => |v| switch (v.target.*) {
                            .slice => |sl| sl.elem,
                            .collection => |c| c.elem_ty,
                            .vec => |vc| vc.elem_ty,
                            else => try self.allocTy(.{ .int = .{ .signed = false, .bits = 8 } }),
                        },
                        else => try self.allocTy(.{ .int = .{ .signed = false, .bits = 8 } }),
                    };
                    const is_mut = switch (base.ty.*) {
                        .slice => |sl| sl.mutable,
                        .collection, .vec => blk: {
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
                    if (base.ty.* == .collection or base.ty.* == .vec or
                        (base.ty.* == .view and (base.ty.view.target.* == .collection or base.ty.view.target.* == .vec)))
                    {
                        const ridx_c = recordOfType(elem);
                        if (ridx_c != null and self.record_defs.items[ridx_c.?].collection_layout != null) {
                            const cl = self.record_defs.items[ridx_c.?].collection_layout.?;
                            if (cl == .soa or cl == .aosoa) {
                                return .{ .ty = try self.allocTy(.{ .collection = .{ .elem_record = ridx_c, .elem_ty = elem } }), .range = null };
                            }
                        }
                    }
                    return .{ .ty = try self.allocTy(.{ .slice = .{ .mutable = is_mut, .elem = elem } }), .range = null };
                }
                _ = try self.checkExpr(ix.idx, null);
                self.in_projection_base = prev_proj;
                const elem: *const Ty = switch (base.ty.*) {
                    .slice => |sl| sl.elem,
                    .collection => |c| c.elem_ty,
                    .vec => |v| v.elem_ty,
                    .view => |v| switch (v.target.*) {
                        .slice => |sl| sl.elem,
                        .collection => |c| c.elem_ty,
                        .vec => |vc| vc.elem_ty,
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
                const resolved_ridx: ?usize = blk: {
                    if (rl.path.len >= 2) {
                        const mod_alias = rl.path[0].slice(self.source);
                        const tname = rl.path[rl.path.len - 1].slice(self.source);
                        if (self.resolveImportedModule(self.current_module_id, mod_alias)) |target_mod| {
                            if (self.findRecordInModule(target_mod, tname)) |ri| {
                                if (!self.record_defs.items[ri].is_pub and target_mod != self.current_module_id) {
                                    self.addError(.visibility_error, rl.span, "cannot construct private record from imported module");
                                }
                                break :blk ri;
                            }
                        }
                    }
                    if (rl.path.len > 0) {
                        const name = rl.path[rl.path.len - 1].slice(self.source);
                        break :blk self.resolveVisibleRecordIndex(name, rl.path[0]);
                    }
                    break :blk null;
                };
                if (resolved_ridx) |ridx| {
                    try self.resolved_records.put(self.alloc, expr, ridx);
                    const rdef = self.record_defs.items[ridx];
                    var subst: std.StringHashMapUnmanaged(*const Ty) = .empty;
                    if (expected) |exp| {
                        if (exp.* == .applied and exp.applied.kind == .record and exp.applied.decl_idx == ridx) {
                            for (rdef.type_params, 0..) |tp, ti| {
                                if (ti < exp.applied.args.len) try subst.put(self.alloc, tp, exp.applied.args[ti]);
                            }
                        }
                    }
                    for (rl.fields) |rf_init| {
                        const fnm = rf_init.name.slice(self.source);
                        if (self.findRecordField(ridx, fnm)) |fi| {
                            const raw_fty = rdef.fields[fi].ty;
                            const fty = try self.substituteType(raw_fty, &subst);
                            const has_free = containsUnresolvedTypeVar(fty, &subst);
                            if (rf_init.value) |v| {
                                const vr = try self.checkExpr(v, if (has_free) null else fty);
                                const final_vt = if (has_free) try self.finalizeInferredType(v.getSpan(), vr) else vr.ty;
                                if (rdef.type_params.len > 0) {
                                    if (!try self.unifyType(raw_fty, final_vt, &subst)) {
                                        self.addError(.type_mismatch, rf_init.span, "field value does not match generic record type parameter");
                                    }
                                } else {
                                    try self.checkAssignmentValue(rf_init.span, fty, vr);
                                }
                            }
                        } else {
                            self.addError(.unknown_ident, rf_init.name, "unknown field in record literal");
                        }
                    }
                    if (rdef.type_params.len > 0 or rdef.constraints.len > 0) {
                        const targs = try self.alloc.alloc(*const Ty, rdef.type_params.len);
                        for (rdef.type_params, 0..) |tp, ti| {
                            targs[ti] = subst.get(tp) orelse try self.allocTy(.{ .type_var = tp });
                        }
                        const brand = self.resolveBrandForConstraints(rdef.constraints, &subst, rl.span);
                        return .{ .ty = try self.allocTy(.{ .applied = .{
                            .kind = .record,
                            .decl_idx = ridx,
                            .args = targs,
                            .brand_inst = brand,
                        } }), .range = null };
                    }
                    return .{ .ty = try self.allocTy(.{ .record = ridx }), .range = null };
                }
                self.addError(.unknown_type, rl.span, "unknown record type in literal");
                for (rl.fields) |rf_init| {
                    if (rf_init.value) |v| _ = try self.checkExpr(v, null);
                }
                return .{ .ty = try self.allocTy(.err), .range = null };
            },
            .tuple => |tp| {
                if (tp.elems.len == 0) return .{ .ty = try self.allocTy(.unit), .range = null };
                const exp_tup: ?[]const *const Ty = if (expected) |exp|
                    if (exp.* == .tuple and exp.tuple.len == tp.elems.len) exp.tuple else null
                else
                    null;
                const es = try self.alloc.alloc(*const Ty, tp.elems.len);
                for (tp.elems, 0..) |el, i| {
                    const el_exp: ?*const Ty = if (exp_tup) |et| et[i] else null;
                    const er = try self.checkExpr(el, el_exp);
                    if (el_exp) |ee| {
                        try self.checkAssignmentValue(el.getSpan(), ee, er);
                        es[i] = ee;
                    } else {
                        es[i] = try self.finalizeInferredType(el.getSpan(), er);
                    }
                }
                return .{ .ty = try self.allocTy(.{ .tuple = es }), .range = null };
            },
            .list => |ls| {
                var elem_ty: ?*const Ty = if (expected) |exp| switch (exp.*) {
                    .collection => |c| c.elem_ty,
                    .vec => |v| v.elem_ty,
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
                    if (exp.* == .collection or exp.* == .vec) {
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
                const saved_field_ranges = try self.alloc.dupe(FieldRangeEntry, self.field_ranges.items);
                defer {
                    for (0..saved_ranges.len) |si| {
                        if (si < self.scopes.items.len) self.scopes.items[si].range = saved_ranges[si];
                    }
                    self.field_ranges.clearRetainingCapacity();
                    self.field_ranges.appendSlice(self.alloc, saved_field_ranges) catch {};
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
                self.field_ranges.clearRetainingCapacity();
                try self.field_ranges.appendSlice(self.alloc, saved_field_ranges);
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
                    const else_exp = expected orelse if (then_res.ty.* == .fn_ty) then_res.ty else null;
                    const else_res = try self.checkExpr(eb, else_exp);
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
                    const joined_ty = (try self.joinLosslessScalarTy(then_res.ty, else_res.ty)) orelse then_res.ty;
                    return .{
                        .ty = joined_ty,
                        .range = joined_range,
                    };
                }
                return then_res;
            },
            .case_expr => |ce| {
                const sub_types = try self.alloc.alloc(*const Ty, ce.subjects.len);
                for (ce.subjects, 0..) |subj, i| {
                    const subject = try self.checkExpr(subj, null);
                    sub_types[i] = if (hasIntegerPattern(ce.arms, i))
                        (try self.readIntegerOperand(subj, subject)).ty
                    else
                        subject.ty;
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
                    } else {
                        out.ty = try self.mergeCaseArmTy(out.ty, br.ty);
                        if (out.range != null and br.range != null) {
                            out.range = out.range.?.join(br.range.?);
                        }
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
                try self.checkCaseExhaustiveness(ce.span, sub_types, ce.arms);
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
                if (mode == .exclusive and root_name.len > 0) {
                    self.invalidateRootFieldRanges(root_name);
                }

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
                                    if (field_idx) |fi| {
                                        if (fi < self.record_defs.items[ri].address_taken_fields.len) {
                                            self.record_defs.items[ri].address_taken_fields[fi] = true;
                                        }
                                    }
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
            .using_expr => |ue| {
                const pushed = try self.pushUsingInstances(ue.span, ue.instances);
                defer if (pushed) {
                    _ = self.active_using_stack.pop();
                };
                return try self.checkExpr(ue.target, expected);
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

    fn resolveVisibleRecordIndex(self: *Analyzer, local_name: []const u8, err_span: ast.Span) ?usize {
        if (self.findRecordInModule(self.current_module_id, local_name)) |ri| return ri;
        if (self.memberImportTarget(self.current_module_id, local_name)) |target_mod| {
            if (self.findRecordInModule(target_mod, local_name)) |ri| {
                if (!self.record_defs.items[ri].is_pub and target_mod != self.current_module_id) {
                    self.addError(.visibility_error, err_span, "cannot access private record from imported module");
                }
                return ri;
            }
        }
        if (self.module_slices.len == 0) return self.findRecordIndex(local_name);
        return null;
    }

    fn resolveVisibleADTIndex(self: *Analyzer, local_name: []const u8, err_span: ast.Span) ?usize {
        if (self.findADTInModule(self.current_module_id, local_name)) |ai| return ai;
        if (self.memberImportTarget(self.current_module_id, local_name)) |target_mod| {
            if (self.findADTInModule(target_mod, local_name)) |ai| {
                if (!self.adt_defs.items[ai].is_pub and target_mod != self.current_module_id) {
                    self.addError(.visibility_error, err_span, "cannot access private ADT from imported module");
                }
                return ai;
            }
        }
        if (self.module_slices.len == 0) return self.findADTIndex(local_name);
        return null;
    }

    fn mergeCaseArmTy(self: *Analyzer, acc: *const Ty, nxt: *const Ty) std.mem.Allocator.Error!*const Ty {
        if (acc.* == .err) return nxt;
        if (acc.* == .option and nxt.* == .option) {
            if (acc.option.* == .err and nxt.option.* != .err) return nxt;
        }
        if (acc.* == .result and nxt.* == .result) {
            const ok_ty = if (acc.result.ok.* == .err) nxt.result.ok else acc.result.ok;
            const err_ty = if (acc.result.err.* == .err) nxt.result.err else acc.result.err;
            return try self.allocTy(.{ .result = .{ .ok = ok_ty, .err = err_ty } });
        }
        return acc;
    }

    const CaseIntInterval = struct {
        lo: i128,
        hi: i128,
    };

    fn patIsCatchAll(pat: *const ast.Pattern) bool {
        return switch (pat.*) {
            .wildcard, .ident => true,
            .alias => |al| patIsCatchAll(al.inner),
            .or_pat => |op| blk: {
                for (op.alternatives) |alt| {
                    if (patIsCatchAll(alt)) break :blk true;
                }
                break :blk false;
            },
            .tuple => |tp| blk: {
                for (tp.elems) |el| {
                    if (!patIsCatchAll(el)) break :blk false;
                }
                break :blk true;
            },
            else => false,
        };
    }

    fn flattenPat(self: *Analyzer, pat: *const ast.Pattern, out: *std.ArrayList(*const ast.Pattern)) std.mem.Allocator.Error!void {
        switch (pat.*) {
            .alias => |al| try self.flattenPat(al.inner, out),
            .or_pat => |op| {
                for (op.alternatives) |alt| {
                    try self.flattenPat(alt, out);
                }
            },
            else => try out.append(self.alloc, pat),
        }
    }

    fn evalPatInt(source: [:0]const u8, pat: *const ast.Pattern) ?i128 {
        if (pat.* != .literal) return null;
        const lit = pat.literal;
        if (lit.tok.tag != .int_literal) return null;
        const parsed = int_range.parseIntLiteral(lit.tok.loc.slice(source)) orelse return null;
        if (!lit.negative) {
            if (parsed.value > @as(u128, @intCast(std.math.maxInt(i128)))) return null;
            return @intCast(parsed.value);
        }
        if (parsed.value == @as(u128, 1) << 127) return std.math.minInt(i128);
        if (parsed.value > @as(u128, @intCast(std.math.maxInt(i128)))) return null;
        return -@as(i128, @intCast(parsed.value));
    }

    fn checkCaseExhaustiveness(
        self: *Analyzer,
        span: ast.Span,
        sub_types: []const *const Ty,
        arms: []const ast.CaseArm,
    ) std.mem.Allocator.Error!void {
        if (sub_types.len == 0) return;

        if (sub_types.len > 1) {
            var has_catch_all = false;
            for (arms) |arm| {
                if (arm.guard != null) continue;
                for (arm.alternatives) |row| {
                    var row_all = row.len == sub_types.len;
                    if (row_all) {
                        for (row) |p| {
                            if (!patIsCatchAll(p)) {
                                row_all = false;
                                break;
                            }
                        }
                    }
                    if (row_all) {
                        has_catch_all = true;
                        break;
                    }
                }
                if (has_catch_all) break;
            }
            if (!has_catch_all) {
                self.addError(.non_exhaustive_match, span, "non-exhaustive multi-subject case expression: add a wildcard '_' arm");
            }
            return;
        }

        const st = sub_types[0];
        if (st.* == .err) return;

        var flat_pats: std.ArrayList(*const ast.Pattern) = .empty;
        for (arms) |arm| {
            if (arm.guard != null) continue;
            for (arm.alternatives) |row| {
                if (row.len == 0) continue;
                if (patIsCatchAll(row[0])) return;
                try self.flattenPat(row[0], &flat_pats);
            }
        }
        for (flat_pats.items) |fp| {
            if (patIsCatchAll(fp)) return;
        }

        switch (st.*) {
            .bool => {
                var seen_true = false;
                var seen_false = false;
                for (flat_pats.items) |fp| {
                    if (fp.* == .literal) {
                        if (fp.literal.tok.tag == .kw_true) seen_true = true;
                        if (fp.literal.tok.tag == .kw_false) seen_false = true;
                    }
                }
                if (!seen_true or !seen_false) {
                    const missing: []const u8 = if (!seen_true and !seen_false)
                        "true, false"
                    else if (!seen_true)
                        "true"
                    else
                        "false";
                    const msg = try std.fmt.allocPrint(self.alloc, "non-exhaustive case on bool: missing pattern(s): {s}", .{missing});
                    self.addError(.non_exhaustive_match, span, msg);
                }
            },
            .option => {
                var seen_some = false;
                var seen_none = false;
                for (flat_pats.items) |fp| {
                    if (fp.* == .constructor) {
                        const c = fp.constructor;
                        const vn = if (c.path.len > 0) c.path[c.path.len - 1].slice(self.source) else "";
                        if (std.mem.eql(u8, vn, "None")) {
                            seen_none = true;
                        } else if (std.mem.eql(u8, vn, "Some")) {
                            if (c.args.len == 0 or patIsCatchAll(c.args[0].pattern)) {
                                seen_some = true;
                            }
                        }
                    }
                }
                if (!seen_some or !seen_none) {
                    const missing: []const u8 = if (!seen_some and !seen_none)
                        "Some(_), None"
                    else if (!seen_some)
                        "Some(_)"
                    else
                        "None";
                    const msg = try std.fmt.allocPrint(self.alloc, "non-exhaustive case on Option: missing pattern(s): {s}", .{missing});
                    self.addError(.non_exhaustive_match, span, msg);
                }
            },
            .result => {
                var seen_ok = false;
                var seen_err = false;
                for (flat_pats.items) |fp| {
                    if (fp.* == .constructor) {
                        const c = fp.constructor;
                        const vn = if (c.path.len > 0) c.path[c.path.len - 1].slice(self.source) else "";
                        if (std.mem.eql(u8, vn, "Ok")) {
                            if (c.args.len == 0 or patIsCatchAll(c.args[0].pattern)) seen_ok = true;
                        } else if (std.mem.eql(u8, vn, "Err")) {
                            if (c.args.len == 0 or patIsCatchAll(c.args[0].pattern)) seen_err = true;
                        }
                    }
                }
                if (!seen_ok or !seen_err) {
                    const missing: []const u8 = if (!seen_ok and !seen_err)
                        "Ok(_), Err(_)"
                    else if (!seen_ok)
                        "Ok(_)"
                    else
                        "Err(_)";
                    const msg = try std.fmt.allocPrint(self.alloc, "non-exhaustive case on Result: missing pattern(s): {s}", .{missing});
                    self.addError(.non_exhaustive_match, span, msg);
                }
            },
            .adt => |aidx| {
                const adt_def = self.adt_defs.items[aidx];
                const covered = try self.alloc.alloc(bool, adt_def.variants.len);
                @memset(covered, false);
                for (flat_pats.items) |fp| {
                    if (fp.* == .constructor) {
                        const c = fp.constructor;
                        const vn = if (c.path.len > 0) c.path[c.path.len - 1].slice(self.source) else "";
                        var args_ok = true;
                        for (c.args) |pa| {
                            if (!patIsCatchAll(pa.pattern)) {
                                args_ok = false;
                                break;
                            }
                        }
                        if (args_ok) {
                            for (adt_def.variants, 0..) |v, vi| {
                                if (std.mem.eql(u8, v.name, vn)) covered[vi] = true;
                            }
                        }
                    }
                }
                var missing_buf: std.ArrayList(u8) = .empty;
                for (adt_def.variants, 0..) |v, vi| {
                    if (!covered[vi]) {
                        if (missing_buf.items.len > 0) try missing_buf.appendSlice(self.alloc, ", ");
                        try missing_buf.appendSlice(self.alloc, v.name);
                    }
                }
                if (missing_buf.items.len > 0) {
                    const msg = try std.fmt.allocPrint(self.alloc, "non-exhaustive case on {s}: missing variant(s): {s}", .{ adt_def.local_name, missing_buf.items });
                    self.addError(.non_exhaustive_match, span, msg);
                }
            },
            .int, .int_range => {
                const dom_opt = st.rangeOf();
                if (dom_opt != null and dom_opt.? == .bounded) {
                    const dom = dom_opt.?.bounded;
                    var intervals: std.ArrayList(CaseIntInterval) = .empty;
                    for (flat_pats.items) |fp| {
                        switch (fp.*) {
                            .literal => {
                                if (evalPatInt(self.source, fp)) |v| {
                                    try intervals.append(self.alloc, .{ .lo = v, .hi = v });
                                }
                            },
                            .range => |rg| {
                                const lo_v = evalPatInt(self.source, rg.lo) orelse continue;
                                const raw_hi = evalPatInt(self.source, rg.hi) orelse continue;
                                const hi_v = if (rg.inclusive)
                                    raw_hi
                                else if (raw_hi > std.math.minInt(i128))
                                    raw_hi - 1
                                else
                                    continue;
                                if (lo_v <= hi_v) {
                                    try intervals.append(self.alloc, .{ .lo = lo_v, .hi = hi_v });
                                }
                            },
                            else => {},
                        }
                    }
                    std.mem.sort(CaseIntInterval, intervals.items, {}, struct {
                        fn lessThan(_: void, a: CaseIntInterval, b: CaseIntInterval) bool {
                            if (a.lo != b.lo) return a.lo < b.lo;
                            return a.hi < b.hi;
                        }
                    }.lessThan);
                    var cur: i128 = dom.lo;
                    var all_covered = false;
                    for (intervals.items) |iv| {
                        if (iv.hi < cur) continue;
                        if (iv.lo > cur) break;
                        if (iv.hi >= dom.hi) {
                            all_covered = true;
                            break;
                        }
                        cur = iv.hi + 1;
                    }
                    if (!all_covered) {
                        const msg = try std.fmt.allocPrint(self.alloc, "non-exhaustive case on integer range {d}..={d}: missing value {d}", .{ dom.lo, dom.hi, cur });
                        self.addError(.non_exhaustive_match, span, msg);
                    }
                } else {
                    self.addError(.non_exhaustive_match, span, "non-exhaustive case on integer type: add a wildcard '_' arm");
                }
            },
            else => {
                self.addError(.non_exhaustive_match, span, "non-exhaustive case expression: add a wildcard '_' arm");
            },
        }
    }

    fn lookupConstructorVariant(self: *const Analyzer, path: []const ast.Span, expected_ty: *const Ty) ?VariantInfo {
        if (path.len == 0) return null;
        const vname = path[path.len - 1].slice(self.source);
        if (path.len >= 3) {
            const mod_alias = path[0].slice(self.source);
            const adt_name = path[path.len - 2].slice(self.source);
            if (self.resolveImportedModule(self.current_module_id, mod_alias)) |target_mod| {
                if (self.findADTInModule(target_mod, adt_name)) |aidx| {
                    for (self.adt_defs.items[aidx].variants) |v| {
                        if (std.mem.eql(u8, v.name, vname)) return v;
                    }
                }
            }
        }
        if (path.len >= 2) {
            const qname = path[path.len - 2].slice(self.source);
            if (self.resolveImportedModule(self.current_module_id, qname)) |target_mod| {
                for (self.adt_defs.items) |adt_def| {
                    if (adt_def.module_id != target_mod) continue;
                    for (adt_def.variants) |v| {
                        if (std.mem.eql(u8, v.name, vname)) return v;
                    }
                }
            }
            if (self.findADTInModule(self.current_module_id, qname)) |aidx| {
                for (self.adt_defs.items[aidx].variants) |v| {
                    if (std.mem.eql(u8, v.name, vname)) return v;
                }
            }
            if (self.findADTIndex(qname)) |aidx| {
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
            if (self.module_slices.len > 0 and adt_def.module_id != self.current_module_id) {
                if (!adt_def.is_pub) continue;
            }
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
            if (adt_def.module_id != self.current_module_id) continue;
            for (adt_def.variants) |v| {
                if (std.mem.eql(u8, v.name, variant_name)) {
                    return self.allocTy(.{ .adt = aidx }) catch null;
                }
            }
        }
        if (self.memberImportTarget(self.current_module_id, variant_name)) |target_mod| {
            for (self.adt_defs.items, 0..) |adt_def, aidx| {
                if (adt_def.module_id != target_mod) continue;
                for (adt_def.variants) |v| {
                    if (std.mem.eql(u8, v.name, variant_name)) {
                        return self.allocTy(.{ .adt = aidx }) catch null;
                    }
                }
            }
        }
        if (self.module_slices.len == 0) {
            for (self.adt_defs.items, 0..) |adt_def, aidx| {
                for (adt_def.variants) |v| {
                    if (std.mem.eql(u8, v.name, variant_name)) {
                        return self.allocTy(.{ .adt = aidx }) catch null;
                    }
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
            .using_expr => |ue| try self.collectFreeRefsExprScoped(ue.target, locals, out),
            .todo_expr => |td| if (td.message) |m| try self.collectFreeRefsExprScoped(m, locals, out),
            .panic_expr => |pn| if (pn.message) |m| try self.collectFreeRefsExprScoped(m, locals, out),
            else => {},
        }
    }

    fn pushUsingInstances(self: *Analyzer, span: ast.Span, inst_paths: []const []const ast.Span) std.mem.Allocator.Error!bool {
        var resolved: std.ArrayList(usize) = .empty;
        for (inst_paths) |path| {
            if (path.len == 0) continue;
            const tail_name = path[path.len - 1].slice(self.source);
            var found: ?usize = null;
            if (path.len >= 2) {
                const qual = path[0].slice(self.source);
                if (self.resolveImportedModule(self.current_module_id, qual)) |tmod| {
                    for (self.instance_defs.items, 0..) |id, ii| {
                        if (id.module_id == tmod and std.mem.eql(u8, id.local_name, tail_name)) {
                            if (!id.is_pub and tmod != self.current_module_id) {
                                self.addError(.visibility_error, path[path.len - 1], "cannot use private instance from imported module");
                            }
                            found = ii;
                            break;
                        }
                    }
                }
            } else {
                for (self.instance_defs.items, 0..) |id, ii| {
                    if (id.module_id == self.current_module_id and std.mem.eql(u8, id.local_name, tail_name)) {
                        found = ii;
                        break;
                    }
                }
                if (found == null) {
                    if (self.memberImportTarget(self.current_module_id, tail_name)) |tmod| {
                        for (self.instance_defs.items, 0..) |id, ii| {
                            if (id.module_id == tmod and std.mem.eql(u8, id.local_name, tail_name)) {
                                if (!id.is_pub and tmod != self.current_module_id) {
                                    self.addError(.visibility_error, path[0], "cannot use private instance from imported module");
                                }
                                found = ii;
                                break;
                            }
                        }
                    }
                }
                if (found == null and self.module_slices.len == 0) {
                    found = self.findInstanceIndex(tail_name);
                }
            }
            if (found) |ii| {
                try resolved.append(self.alloc, ii);
            } else {
                self.addError(.unknown_ident, span, "unknown trait instance in 'using' clause");
            }
        }
        try self.active_using_stack.append(self.alloc, try resolved.toOwnedSlice(self.alloc));
        return true;
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
        if (right.* == .using_expr) {
            const ue = right.using_expr;
            const pushed = try self.pushUsingInstances(ue.span, ue.instances);
            defer if (pushed) {
                _ = self.active_using_stack.pop();
            };
            if (ue.target.* == .call) {
                const cr = try self.checkCall(ue.target, ue.target.call.span, ue.target.call.callee, ue.target.call.args, left_res, left, expected);
                try self.expr_types.put(self.alloc, ue.target, cr.ty);
                try self.expr_types.put(self.alloc, right, cr.ty);
                return cr;
            }
            const ur = try self.checkExpr(ue.target, expected);
            try self.expr_types.put(self.alloc, right, ur.ty);
            return ur;
        }
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

    fn hktNameFromTy(self: *const Analyzer, ty: *const Ty) ?[]const u8 {
        return switch (ty.*) {
            .option => "Option",
            .applied => |ap| switch (ap.kind) {
                .record => self.record_defs.items[ap.decl_idx].name,
                .adt => self.adt_defs.items[ap.decl_idx].name,
                .opaque_ty => self.opaque_defs.items[ap.decl_idx].name,
            },
            .hkt_app => |ha| ha.ctor,
            else => null,
        };
    }

    fn instantiateReturnBrand(self: *Analyzer, ty: *const Ty, witnesses: []const ResolvedWitness) std.mem.Allocator.Error!*const Ty {
        if (witnesses.len == 0) return ty;
        if (ty.* == .applied) {
            const ap = ty.applied;
            var new_brand = ap.brand_inst;
            var changed = false;
            if (ap.brand_inst) |b| {
                if (std.mem.startsWith(u8, b, "__param_")) {
                    const pidx = std.fmt.parseInt(usize, b["__param_".len..], 10) catch null;
                    if (pidx) |pi| {
                        if (pi < witnesses.len) {
                            new_brand = switch (witnesses[pi]) {
                                .concrete => |cw| self.instance_defs.items[cw.inst_idx].name,
                                .param => |op| try std.fmt.allocPrint(self.alloc, "__param_{d}", .{op}),
                            };
                            changed = true;
                        }
                    }
                }
            }
            if (changed) {
                return try self.allocTy(.{ .applied = .{
                    .kind = ap.kind,
                    .decl_idx = ap.decl_idx,
                    .args = ap.args,
                    .brand_inst = new_brand,
                } });
            }
        }
        return ty;
    }

    fn resolveConstraintsList(
        self: *Analyzer,
        cs: []const ResolvedConstraint,
        subst: *const std.StringHashMapUnmanaged(*const Ty),
        span: ast.Span,
    ) std.mem.Allocator.Error![]const ResolvedWitness {
        var out: std.ArrayList(ResolvedWitness) = .empty;
        for (cs) |rc| {
            const tr = self.trait_defs.items[rc.trait_idx];
            var sub_args = try self.alloc.alloc(*const Ty, rc.args.len);
            var sub_hkts = try self.alloc.alloc(?[]const u8, rc.args.len);
            for (rc.args, 0..) |ca, ci| {
                sub_args[ci] = try self.substituteType(ca, subst);
                const raw_h = if (ci < rc.hkt_arg_names.len) rc.hkt_arg_names[ci] else null;
                if (ci < tr.params.len and tr.params[ci].arity >= 1 and raw_h != null) {
                    const hkey = try std.fmt.allocPrint(self.alloc, "__hkt__{s}", .{raw_h.?});
                    if (subst.get(hkey)) |bound_ty| {
                        sub_hkts[ci] = self.hktNameFromTy(bound_ty) orelse raw_h.?;
                    } else {
                        sub_hkts[ci] = raw_h.?;
                    }
                } else {
                    sub_hkts[ci] = raw_h;
                }
            }
            if (self.resolveTraitWitness(rc.trait_idx, sub_args, sub_hkts, span, true)) |w| {
                try out.append(self.alloc, w);
            }
        }
        return try out.toOwnedSlice(self.alloc);
    }

    fn findTraitMethodCandidate(self: *const Analyzer, cname: []const u8, total_args: usize) ?struct { trait_idx: usize, method: TraitMethodDef } {
        for (self.trait_defs.items, 0..) |tr, ti| {
            if (self.module_slices.len > 0 and tr.module_id != self.current_module_id and !tr.is_pub) {
                if (self.memberImportTarget(self.current_module_id, tr.local_name) == null) continue;
            }
            for (tr.methods) |m| {
                if (std.mem.eql(u8, m.name, cname) and m.params.len == total_args) {
                    return .{ .trait_idx = ti, .method = m };
                }
            }
        }
        return null;
    }

    fn tryCheckTraitMethodCall(
        self: *Analyzer,
        call_expr: *const ast.Expr,
        span: ast.Span,
        cname: []const u8,
        args: []const ast.CallArg,
        piped_recv: ?ExprResult,
        expected: ?*const Ty,
    ) std.mem.Allocator.Error!?ExprResult {
        const recv_off: usize = if (piped_recv != null) 1 else 0;
        const cand = self.findTraitMethodCandidate(cname, args.len + recv_off) orelse return null;
        const tr = self.trait_defs.items[cand.trait_idx];
        const m = cand.method;

        var subst: std.StringHashMapUnmanaged(*const Ty) = .empty;
        if (expected) |exp| {
            if (exp.* != .err) {
                _ = self.unifyType(m.ret, exp, &subst) catch false;
            }
        }
        if (piped_recv) |pr| {
            if (m.params.len > 0) {
                if (!try self.unifyType(m.params[0], pr.ty, &subst)) {
                    self.addError(.type_mismatch, span, "trait method receiver type mismatch");
                }
            }
        }
        for (args, 0..) |arg, ai| {
            const pidx = ai + recv_off;
            const raw_p = m.params[pidx];
            const ep_sub = try self.substituteType(raw_p, &subst);
            const has_free = containsUnresolvedTypeVar(ep_sub, &subst);
            const ar = try self.checkExpr(arg.value, if (has_free) null else ep_sub);
            const final_ar_ty = if (has_free) try self.finalizeInferredType(arg.value.getSpan(), ar) else ar.ty;
            if (!try self.unifyType(raw_p, final_ar_ty, &subst)) {
                self.addError(.type_mismatch, arg.span, "trait method argument type mismatch");
            }
        }

        const t_args = try self.alloc.alloc(*const Ty, tr.params.len);
        const t_hkts = try self.alloc.alloc(?[]const u8, tr.params.len);
        for (tr.params, 0..) |tp, pi| {
            if (tp.arity >= 1) {
                const hkey = try std.fmt.allocPrint(self.alloc, "__hkt__{s}", .{tp.name});
                if (subst.get(hkey)) |hty| {
                    t_hkts[pi] = self.hktNameFromTy(hty);
                } else {
                    t_hkts[pi] = if (self.isHKTActive(tp.name)) tp.name else null;
                }
                t_args[pi] = try self.allocTy(.{ .type_var = tp.name });
            } else {
                t_hkts[pi] = null;
                t_args[pi] = subst.get(tp.name) orelse try self.allocTy(.{ .type_var = tp.name });
            }
        }

        const witness_opt = self.resolveTraitWitness(cand.trait_idx, t_args, t_hkts, span, true);
        if (witness_opt) |w| {
            const m_targs = try self.alloc.alloc(*const Ty, m.type_params.len);
            for (m.type_params, 0..) |tp, ti| {
                m_targs[ti] = subst.get(tp) orelse try self.allocTy(.{ .type_var = tp });
            }
            const empty_ws: []const ResolvedWitness = &.{};
            try self.call_trait_resolutions.put(self.alloc, call_expr, .{
                .kind = .{ .trait_method = .{ .method_name = m.name, .witness = w } },
                .witnesses = empty_ws,
                .type_args = m_targs,
            });
        }
        const ret_ty = try self.substituteType(m.ret, &subst);
        return .{ .ty = ret_ty, .range = ret_ty.rangeOf() };
    }

    fn collectionElemTy(ty: *const Ty) ?*const Ty {
        return switch (ty.*) {
            .collection => |c| c.elem_ty,
            .vec => |v| v.elem_ty,
            .slice => |s| s.elem,
            .view => |v| switch (v.target.*) {
                .collection => |c| c.elem_ty,
                .vec => |vc| vc.elem_ty,
                .slice => |s| s.elem,
                else => null,
            },
            .path_borrow => |pb| switch (pb.base.*) {
                .collection => |c| c.elem_ty,
                .vec => |vc| vc.elem_ty,
                .slice => |s| s.elem,
                else => null,
            },
            else => null,
        };
    }

    fn moduleKeyOf(self: *const Analyzer, mod_id: usize) ?[]const u8 {
        for (self.module_slices) |sl| {
            if (sl.module_id == mod_id) return sl.module_key;
        }
        return null;
    }

    const StdModuleNs = enum { vec, map, set, deque, str };

    fn stdModuleNsOfKey(mkey: []const u8) ?StdModuleNs {
        if (std.mem.eql(u8, mkey, "std/vec")) return .vec;
        if (std.mem.eql(u8, mkey, "std/map")) return .map;
        if (std.mem.eql(u8, mkey, "std/set")) return .set;
        if (std.mem.eql(u8, mkey, "std/deque")) return .deque;
        if (std.mem.eql(u8, mkey, "std/str")) return .str;
        return null;
    }

    fn resolveStdNsForCall(self: *Analyzer, callee: *const ast.Expr) ?struct { ns: StdModuleNs, method: []const u8 } {
        switch (callee.*) {
            .field => |fld| {
                if (fld.target.* != .ident) return null;
                const qname = fld.target.ident.slice(self.source);
                const mname = fld.name.slice(self.source);
                if (self.resolveImportedModule(self.current_module_id, qname)) |target_mod| {
                    const mkey = self.moduleKeyOf(target_mod) orelse return null;
                    const ns = stdModuleNsOfKey(mkey) orelse return null;
                    return .{ .ns = ns, .method = mname };
                }
                if (self.lookupVar(qname) == null) {
                    if (std.mem.eql(u8, qname, "vec")) return .{ .ns = .vec, .method = mname };
                    if (std.mem.eql(u8, qname, "map")) return .{ .ns = .map, .method = mname };
                    if (std.mem.eql(u8, qname, "set")) return .{ .ns = .set, .method = mname };
                    if (std.mem.eql(u8, qname, "deque")) return .{ .ns = .deque, .method = mname };
                    if (std.mem.eql(u8, qname, "str")) return .{ .ns = .str, .method = mname };
                }
                return null;
            },
            .ident => |sp| {
                const mname = sp.slice(self.source);
                if (self.memberImportTarget(self.current_module_id, mname)) |target_mod| {
                    const mkey = self.moduleKeyOf(target_mod) orelse return null;
                    const ns = stdModuleNsOfKey(mkey) orelse return null;
                    return .{ .ns = ns, .method = mname };
                }
                return null;
            },
            else => return null,
        }
    }

    fn extractDynVecBorrowRoot(self: *Analyzer, expr: *const ast.Expr) ?[]const u8 {
        switch (expr.*) {
            .index => |ix| {
                if (self.extractRootIdent(ix.target)) |rn| {
                    if (self.lookupVar(rn)) |vb| {
                        if (vb.ty.* == .vec or (vb.ty.* == .view and vb.ty.view.target.* == .vec)) return rn;
                    }
                }
                return null;
            },
            .call => |c| {
                if (self.resolveStdNsForCall(c.callee)) |info| {
                    if (info.ns == .vec and (std.mem.eql(u8, info.method, "as_slice") or std.mem.eql(u8, info.method, "as_collection")) and c.args.len >= 1) {
                        return self.extractRootIdent(c.args[0].value);
                    }
                }
                return null;
            },
            else => return null,
        }
    }

    fn attachSharedBorrowBinding(
        self: *Analyzer,
        vb: *Binding,
        root_name: []const u8,
        span: ast.Span,
    ) std.mem.Allocator.Error!void {
        _ = span;
        const vid = self.next_view_id;
        self.next_view_id += 1;
        try self.active_views.append(self.alloc, .{
            .id = vid,
            .binding_name = vb.name,
            .root_name = root_name,
            .record_idx = null,
            .field_idx = null,
            .index_key = null,
            .perm = .shared,
            .active = true,
            .is_sentinel = false,
            .in_trace = false,
        });
        vb.view_id = vid;
        vb.view_root = root_name;
    }

    fn checkDynamicContainerMut(
        self: *Analyzer,
        span: ast.Span,
        recv_expr: *const ast.Expr,
        allow_active_views: bool,
    ) std.mem.Allocator.Error!bool {
        const resolved = self.resolveAccessRoot(recv_expr);
        const rn = resolved.root_name orelse {
            self.addError(.mutability_error, span, "dynamic container mutation requires a mutable binding or Exclusive View");
            return false;
        };
        const vb = self.lookupVar(rn) orelse return false;
        if (vb.moved) {
            self.addError(.use_after_move, recv_expr.getSpan(), "use of moved dynamic container");
            return false;
        }
        const is_excl_view = vb.ty.* == .view and vb.ty.view.mode == .exclusive;
        const is_shared_view = vb.ty.* == .view and vb.ty.view.mode == .shared;
        if (is_shared_view) {
            self.addError(.borrow_conflict, span, "cannot mutate or reallocate dynamic container through a shared View");
            return false;
        }
        if (!vb.mutable and !is_excl_view) {
            self.addError(.mutability_error, span, "cannot mutate immutable dynamic container; mark binding 'mut'");
            return false;
        }
        if (!allow_active_views) {
            for (self.active_views.items) |av| {
                if (!av.active) continue;
                if (std.mem.eql(u8, av.root_name, rn)) {
                    self.addError(.borrow_conflict, span, "cannot grow, shrink, or reallocate dynamic container while an active view borrows from it");
                    return false;
                }
            }
        }
        try self.recordAccess(rn, recordOfType(vb.ty), null, true, span, null, resolved.through_view_id);
        return true;
    }

    fn recordDynamicContainerRead(self: *Analyzer, span: ast.Span, recv_expr: *const ast.Expr) std.mem.Allocator.Error!void {
        const resolved = self.resolveAccessRoot(recv_expr);
        if (resolved.root_name) |rn| {
            if (self.lookupVar(rn)) |vb| {
                try self.recordAccess(rn, recordOfType(vb.ty), null, false, span, null, resolved.through_view_id);
            }
        }
    }

    fn tryCheckStdIntrinsicCall(
        self: *Analyzer,
        call_expr: *const ast.Expr,
        span: ast.Span,
        callee: *const ast.Expr,
        args: []const ast.CallArg,
        piped_recv: ?ExprResult,
        piped_recv_expr: ?*const ast.Expr,
        expected: ?*const Ty,
    ) std.mem.Allocator.Error!?ExprResult {
        const ns_info = self.resolveStdNsForCall(callee) orelse return null;
        const mname = ns_info.method;
        const unit_ty = try self.allocTy(.unit);
        const bool_ty = try self.allocTy(.bool);
        const u64_ty = try self.allocTy(.{ .int = .{ .signed = false, .bits = 64 } });
        const u8_ty = try self.allocTy(.{ .int = .{ .signed = false, .bits = 8 } });
        const str_ty = try self.allocTy(.string);

        switch (ns_info.ns) {
            .str => {
                const recv_offset: usize = if (piped_recv != null) 0 else 1;
                const s0_res = piped_recv orelse blk: {
                    if (args.len < 1) return null;
                    break :blk try self.checkExpr(args[0].value, str_ty);
                };
                try self.checkAssignmentValue(span, str_ty, s0_res);
                if (std.mem.eql(u8, mname, "len") and args.len == recv_offset) {
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .str_len, .container_ty = str_ty });
                    return .{ .ty = u64_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "is_empty") and args.len == recv_offset) {
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .str_is_empty, .container_ty = str_ty });
                    return .{ .ty = bool_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "eq") and args.len == recv_offset + 1) {
                    const s1 = try self.checkExpr(args[recv_offset].value, str_ty);
                    try self.checkAssignmentValue(args[recv_offset].span, str_ty, s1);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .str_eq, .container_ty = str_ty });
                    return .{ .ty = bool_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "concat") and args.len == recv_offset + 1) {
                    const s1 = try self.checkExpr(args[recv_offset].value, str_ty);
                    try self.checkAssignmentValue(args[recv_offset].span, str_ty, s1);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .str_concat, .container_ty = str_ty });
                    return .{ .ty = str_ty, .range = null };
                } else if ((std.mem.eql(u8, mname, "starts_with") or std.mem.eql(u8, mname, "ends_with") or std.mem.eql(u8, mname, "contains")) and args.len == recv_offset + 1) {
                    const s1 = try self.checkExpr(args[recv_offset].value, str_ty);
                    try self.checkAssignmentValue(args[recv_offset].span, str_ty, s1);
                    const kind: StdIntrinsicKind = if (std.mem.eql(u8, mname, "starts_with"))
                        .str_starts_with
                    else if (std.mem.eql(u8, mname, "ends_with"))
                        .str_ends_with
                    else
                        .str_contains;
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = kind, .container_ty = str_ty });
                    return .{ .ty = bool_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "byte_at") and args.len == recv_offset + 1) {
                    _ = try self.checkExpr(args[recv_offset].value, null);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .str_byte_at, .container_ty = str_ty });
                    return .{ .ty = try self.allocTy(.{ .option = u8_ty }), .range = null };
                } else if (std.mem.eql(u8, mname, "slice_bytes") and args.len == recv_offset + 2) {
                    _ = try self.checkExpr(args[recv_offset].value, null);
                    _ = try self.checkExpr(args[recv_offset + 1].value, null);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .str_slice_bytes, .container_ty = str_ty });
                    return .{ .ty = str_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "repeat") and args.len == recv_offset + 1) {
                    const cnt_res = try self.checkExpr(args[recv_offset].value, null);
                    try self.checkAssignmentValue(args[recv_offset].span, u64_ty, cnt_res);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .str_repeat, .container_ty = str_ty });
                    return .{ .ty = str_ty, .range = null };
                }
                return null;
            },
            .vec => {
                if (piped_recv == null and (std.mem.eql(u8, mname, "new") or std.mem.eql(u8, mname, "with_capacity"))) {
                    const is_cap = std.mem.eql(u8, mname, "with_capacity");
                    if ((is_cap and args.len != 1) or (!is_cap and args.len != 0)) {
                        self.addError(.type_mismatch, span, "invalid argument count for vec constructor");
                        return .{ .ty = try self.allocTy(.err), .range = null };
                    }
                    const cap_res = if (is_cap) try self.checkExpr(args[0].value, null) else null;
                    if (expected != null and expected.?.* == .vec) {
                        if (cap_res) |cr_val| {
                            if (cr_val.range) |cr| {
                                if (cr == .bounded and cr.bounded.lo == cr.bounded.hi and cr.bounded.lo >= 0) {
                                    if (std.math.cast(usize, cr.bounded.lo)) |n| {
                                        if (recordOfType(expected.?.vec.elem_ty)) |ridx| {
                                            const cur = self.record_defs.items[ridx].observed_collection_len;
                                            self.record_defs.items[ridx].observed_collection_len = if (cur) |c| @max(c, n) else n;
                                        }
                                    }
                                }
                            }
                        }
                        try self.std_intrinsic_calls.put(self.alloc, call_expr, .{
                            .kind = if (is_cap) .vec_with_capacity else .vec_new,
                            .container_ty = expected.?,
                        });
                        return .{ .ty = expected.?, .range = null };
                    }
                    self.addError(.type_mismatch, span, "cannot infer element type of vec constructor; add annotation like 'let mut xs: Vec(u32) = vec.new()'");
                    return .{ .ty = try self.allocTy(.err), .range = null };
                }
                const recv_offset: usize = if (piped_recv != null) 0 else 1;
                if (piped_recv == null and args.len < 1) return null;
                const recv_expr = piped_recv_expr orelse args[0].value;
                const recv_res = piped_recv orelse try self.checkExpr(args[0].value, null);
                const recv_is_ptr = recv_res.ty.* == .view;
                const inner_ty = if (recv_res.ty.* == .view) recv_res.ty.view.target else recv_res.ty;
                if (inner_ty.* != .vec) {
                    if (inner_ty.* != .err) {
                        self.addError(.type_mismatch, recv_expr.getSpan(), "vec operation requires a Vec(T) or View(Vec(T), ...)");
                    }
                    return .{ .ty = try self.allocTy(.err), .range = null };
                }
                const elem_ty = inner_ty.vec.elem_ty;

                if (std.mem.eql(u8, mname, "len") and args.len == recv_offset) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .vec_len, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = u64_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "capacity") and args.len == recv_offset) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .vec_capacity, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = u64_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "is_empty") and args.len == recv_offset) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .vec_is_empty, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = bool_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "get") and args.len == recv_offset + 1) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    _ = try self.checkExpr(args[recv_offset].value, null);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .vec_get, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = try self.allocTy(.{ .option = elem_ty }), .range = null };
                } else if (std.mem.eql(u8, mname, "as_slice") and args.len == recv_offset) {
                    if (inner_ty.vec.elem_record) |ri| {
                        if (self.record_defs.items[ri].collection_layout) |cl| {
                            if (cl == .soa or cl == .aosoa) {
                                self.addError(.invalid_ffi_type, span, "vec.as_slice requires AoS backing; use vec.as_collection(...) for @layout(soa)/@layout(aosoa) vectors");
                            }
                        }
                    }
                    try self.recordDynamicContainerRead(span, recv_expr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .vec_as_slice, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = try self.allocTy(.{ .slice = .{ .mutable = false, .elem = elem_ty } }), .range = null };
                } else if (std.mem.eql(u8, mname, "as_mut_slice") and args.len == recv_offset) {
                    if (inner_ty.vec.elem_record) |ri| {
                        if (self.record_defs.items[ri].collection_layout) |cl| {
                            if (cl == .soa or cl == .aosoa) {
                                self.addError(.invalid_ffi_type, span, "vec.as_mut_slice requires AoS backing; use vec.as_collection(...) for @layout(soa)/@layout(aosoa) vectors");
                            }
                        }
                    }
                    _ = try self.checkDynamicContainerMut(span, recv_expr, true);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .vec_as_mut_slice, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = try self.allocTy(.{ .slice = .{ .mutable = true, .elem = elem_ty } }), .range = null };
                } else if (std.mem.eql(u8, mname, "as_collection") and args.len == recv_offset) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    const col_ty = try self.allocTy(.{ .collection = .{ .elem_record = inner_ty.vec.elem_record, .elem_ty = elem_ty } });
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .vec_as_collection, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = col_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "push") and args.len == recv_offset + 1) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    const vr = try self.checkExpr(args[recv_offset].value, elem_ty);
                    try self.checkAssignmentValue(args[recv_offset].span, elem_ty, vr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .vec_push, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = unit_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "pop") and args.len == recv_offset) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .vec_pop, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = try self.allocTy(.{ .option = elem_ty }), .range = null };
                } else if (std.mem.eql(u8, mname, "set") and args.len == recv_offset + 2) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, true);
                    _ = try self.checkExpr(args[recv_offset].value, null);
                    const vr = try self.checkExpr(args[recv_offset + 1].value, elem_ty);
                    try self.checkAssignmentValue(args[recv_offset + 1].span, elem_ty, vr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .vec_set, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = bool_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "swap_remove") and args.len == recv_offset + 1) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    _ = try self.checkExpr(args[recv_offset].value, null);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .vec_swap_remove, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = try self.allocTy(.{ .option = elem_ty }), .range = null };
                } else if (std.mem.eql(u8, mname, "reserve") and args.len == recv_offset + 1) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    _ = try self.checkExpr(args[recv_offset].value, null);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .vec_reserve, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = unit_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "clear") and args.len == recv_offset) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .vec_clear, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = unit_ty, .range = null };
                }
                return null;
            },
            .map => {
                if (piped_recv == null and (std.mem.eql(u8, mname, "new") or std.mem.eql(u8, mname, "with_capacity"))) {
                    const is_cap = std.mem.eql(u8, mname, "with_capacity");
                    if ((is_cap and args.len != 1) or (!is_cap and args.len != 0)) {
                        self.addError(.type_mismatch, span, "invalid argument count for map constructor");
                        return .{ .ty = try self.allocTy(.err), .range = null };
                    }
                    if (is_cap) _ = try self.checkExpr(args[0].value, null);
                    if (expected != null and expected.?.* == .map) {
                        try self.std_intrinsic_calls.put(self.alloc, call_expr, .{
                            .kind = if (is_cap) .map_with_capacity else .map_new,
                            .container_ty = expected.?,
                        });
                        return .{ .ty = expected.?, .range = null };
                    }
                    self.addError(.type_mismatch, span, "cannot infer Map(K, V) type; add annotation like 'let mut m: Map(String, u32) = map.new()'");
                    return .{ .ty = try self.allocTy(.err), .range = null };
                }
                const recv_offset: usize = if (piped_recv != null) 0 else 1;
                if (piped_recv == null and args.len < 1) return null;
                const recv_expr = piped_recv_expr orelse args[0].value;
                const recv_res = piped_recv orelse try self.checkExpr(args[0].value, null);
                const recv_is_ptr = recv_res.ty.* == .view;
                const inner_ty = if (recv_res.ty.* == .view) recv_res.ty.view.target else recv_res.ty;
                if (inner_ty.* != .map) {
                    if (inner_ty.* != .err) {
                        self.addError(.type_mismatch, recv_expr.getSpan(), "map operation requires a Map(K, V) or View(Map(K, V), ...)");
                    }
                    return .{ .ty = try self.allocTy(.err), .range = null };
                }
                const key_ty = inner_ty.map.key_ty;
                const val_ty = inner_ty.map.val_ty;

                if (std.mem.eql(u8, mname, "len") and args.len == recv_offset) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .map_len, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = u64_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "is_empty") and args.len == recv_offset) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .map_is_empty, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = bool_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "get") and args.len == recv_offset + 1) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    const kr = try self.checkExpr(args[recv_offset].value, key_ty);
                    try self.checkAssignmentValue(args[recv_offset].span, key_ty, kr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .map_get, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = try self.allocTy(.{ .option = val_ty }), .range = null };
                } else if (std.mem.eql(u8, mname, "contains") and args.len == recv_offset + 1) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    const kr = try self.checkExpr(args[recv_offset].value, key_ty);
                    try self.checkAssignmentValue(args[recv_offset].span, key_ty, kr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .map_contains, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = bool_ty, .range = null };
                } else if ((std.mem.eql(u8, mname, "insert") or std.mem.eql(u8, mname, "put")) and args.len == recv_offset + 2) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    const kr = try self.checkExpr(args[recv_offset].value, key_ty);
                    try self.checkAssignmentValue(args[recv_offset].span, key_ty, kr);
                    const vr = try self.checkExpr(args[recv_offset + 1].value, val_ty);
                    try self.checkAssignmentValue(args[recv_offset + 1].span, val_ty, vr);
                    const is_put = std.mem.eql(u8, mname, "put");
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{
                        .kind = if (is_put) .map_put else .map_insert,
                        .container_ty = inner_ty,
                        .recv_is_ptr = recv_is_ptr,
                    });
                    return .{ .ty = if (is_put) unit_ty else try self.allocTy(.{ .option = val_ty }), .range = null };
                } else if (std.mem.eql(u8, mname, "remove") and args.len == recv_offset + 1) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    const kr = try self.checkExpr(args[recv_offset].value, key_ty);
                    try self.checkAssignmentValue(args[recv_offset].span, key_ty, kr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .map_remove, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = try self.allocTy(.{ .option = val_ty }), .range = null };
                } else if (std.mem.eql(u8, mname, "clear") and args.len == recv_offset) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .map_clear, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = unit_ty, .range = null };
                }
                return null;
            },
            .set => {
                if (piped_recv == null and (std.mem.eql(u8, mname, "new") or std.mem.eql(u8, mname, "with_capacity"))) {
                    const is_cap = std.mem.eql(u8, mname, "with_capacity");
                    if ((is_cap and args.len != 1) or (!is_cap and args.len != 0)) {
                        self.addError(.type_mismatch, span, "invalid argument count for set constructor");
                        return .{ .ty = try self.allocTy(.err), .range = null };
                    }
                    if (is_cap) _ = try self.checkExpr(args[0].value, null);
                    if (expected != null and expected.?.* == .set) {
                        try self.std_intrinsic_calls.put(self.alloc, call_expr, .{
                            .kind = if (is_cap) .set_with_capacity else .set_new,
                            .container_ty = expected.?,
                        });
                        return .{ .ty = expected.?, .range = null };
                    }
                    self.addError(.type_mismatch, span, "cannot infer Set(T) element type; add annotation like 'let mut s: Set(u32) = set.new()'");
                    return .{ .ty = try self.allocTy(.err), .range = null };
                }
                const recv_offset: usize = if (piped_recv != null) 0 else 1;
                if (piped_recv == null and args.len < 1) return null;
                const recv_expr = piped_recv_expr orelse args[0].value;
                const recv_res = piped_recv orelse try self.checkExpr(args[0].value, null);
                const recv_is_ptr = recv_res.ty.* == .view;
                const inner_ty = if (recv_res.ty.* == .view) recv_res.ty.view.target else recv_res.ty;
                if (inner_ty.* != .set) {
                    if (inner_ty.* != .err) {
                        self.addError(.type_mismatch, recv_expr.getSpan(), "set operation requires a Set(T) or View(Set(T), ...)");
                    }
                    return .{ .ty = try self.allocTy(.err), .range = null };
                }
                const elem_ty = inner_ty.set.elem_ty;

                if (std.mem.eql(u8, mname, "len") and args.len == recv_offset) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .set_len, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = u64_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "is_empty") and args.len == recv_offset) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .set_is_empty, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = bool_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "contains") and args.len == recv_offset + 1) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    const er = try self.checkExpr(args[recv_offset].value, elem_ty);
                    try self.checkAssignmentValue(args[recv_offset].span, elem_ty, er);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .set_contains, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = bool_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "insert") and args.len == recv_offset + 1) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    const er = try self.checkExpr(args[recv_offset].value, elem_ty);
                    try self.checkAssignmentValue(args[recv_offset].span, elem_ty, er);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .set_insert, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = bool_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "remove") and args.len == recv_offset + 1) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    const er = try self.checkExpr(args[recv_offset].value, elem_ty);
                    try self.checkAssignmentValue(args[recv_offset].span, elem_ty, er);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .set_remove, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = bool_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "clear") and args.len == recv_offset) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .set_clear, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = unit_ty, .range = null };
                }
                return null;
            },
            .deque => {
                if (piped_recv == null and (std.mem.eql(u8, mname, "new") or std.mem.eql(u8, mname, "with_capacity"))) {
                    const is_cap = std.mem.eql(u8, mname, "with_capacity");
                    if ((is_cap and args.len != 1) or (!is_cap and args.len != 0)) {
                        self.addError(.type_mismatch, span, "invalid argument count for deque constructor");
                        return .{ .ty = try self.allocTy(.err), .range = null };
                    }
                    if (is_cap) _ = try self.checkExpr(args[0].value, null);
                    if (expected != null and expected.?.* == .deque) {
                        try self.std_intrinsic_calls.put(self.alloc, call_expr, .{
                            .kind = if (is_cap) .deque_with_capacity else .deque_new,
                            .container_ty = expected.?,
                        });
                        return .{ .ty = expected.?, .range = null };
                    }
                    self.addError(.type_mismatch, span, "cannot infer Deque(T) element type; add annotation like 'let mut dq: Deque(i32) = deque.new()'");
                    return .{ .ty = try self.allocTy(.err), .range = null };
                }
                const recv_offset: usize = if (piped_recv != null) 0 else 1;
                if (piped_recv == null and args.len < 1) return null;
                const recv_expr = piped_recv_expr orelse args[0].value;
                const recv_res = piped_recv orelse try self.checkExpr(args[0].value, null);
                const recv_is_ptr = recv_res.ty.* == .view;
                const inner_ty = if (recv_res.ty.* == .view) recv_res.ty.view.target else recv_res.ty;
                if (inner_ty.* != .deque) {
                    if (inner_ty.* != .err) {
                        self.addError(.type_mismatch, recv_expr.getSpan(), "deque operation requires a Deque(T) or View(Deque(T), ...)");
                    }
                    return .{ .ty = try self.allocTy(.err), .range = null };
                }
                const elem_ty = inner_ty.deque.elem_ty;

                if (std.mem.eql(u8, mname, "len") and args.len == recv_offset) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .deque_len, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = u64_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "is_empty") and args.len == recv_offset) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .deque_is_empty, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = bool_ty, .range = null };
                } else if (std.mem.eql(u8, mname, "get") and args.len == recv_offset + 1) {
                    try self.recordDynamicContainerRead(span, recv_expr);
                    _ = try self.checkExpr(args[recv_offset].value, null);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .deque_get, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = try self.allocTy(.{ .option = elem_ty }), .range = null };
                } else if ((std.mem.eql(u8, mname, "push_back") or std.mem.eql(u8, mname, "push_front")) and args.len == recv_offset + 1) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    const er = try self.checkExpr(args[recv_offset].value, elem_ty);
                    try self.checkAssignmentValue(args[recv_offset].span, elem_ty, er);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{
                        .kind = if (std.mem.eql(u8, mname, "push_back")) .deque_push_back else .deque_push_front,
                        .container_ty = inner_ty,
                        .recv_is_ptr = recv_is_ptr,
                    });
                    return .{ .ty = unit_ty, .range = null };
                } else if ((std.mem.eql(u8, mname, "pop_front") or std.mem.eql(u8, mname, "pop_back")) and args.len == recv_offset) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{
                        .kind = if (std.mem.eql(u8, mname, "pop_front")) .deque_pop_front else .deque_pop_back,
                        .container_ty = inner_ty,
                        .recv_is_ptr = recv_is_ptr,
                    });
                    return .{ .ty = try self.allocTy(.{ .option = elem_ty }), .range = null };
                } else if (std.mem.eql(u8, mname, "clear") and args.len == recv_offset) {
                    _ = try self.checkDynamicContainerMut(span, recv_expr, false);
                    try self.std_intrinsic_calls.put(self.alloc, call_expr, .{ .kind = .deque_clear, .container_ty = inner_ty, .recv_is_ptr = recv_is_ptr });
                    return .{ .ty = unit_ty, .range = null };
                }
                return null;
            },
        }
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

        // Standard library compiler-managed dynamic containers & String intrinsics (`std/vec`, `std/map`, `std/set`, `std/deque`, `std/str`).
        if (try self.tryCheckStdIntrinsicCall(call_expr, span, callee, args, piped_recv, piped_recv_expr, expected)) |std_res| {
            return std_res;
        }

        // Special-case collection/option/result higher-order combinators (`map_in_place`, `fold`, `map`, `and_then`, `unwrap_or`, `ok_or`).
        if (callee.* == .ident) {
            const cname = callee.ident.slice(self.source);
            if (self.active_using_stack.items.len > 0) {
                if (self.findTraitMethodCandidate(cname, args.len + (if (piped_recv != null) @as(usize, 1) else 0)) != null) {
                    if (try self.tryCheckTraitMethodCall(call_expr, span, cname, args, piped_recv, expected)) |tres| {
                        return tres;
                    }
                }
            }
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
        }

        if (self.resolveCalleeFnIndex(callee, true)) |fidx| {
            const fsig = self.fn_sigs.items[fidx];
            try self.resolved_fn_calls.put(self.alloc, callee, fsig.name);
            const recv_offset: usize = if (piped_recv != null) 1 else 0;
            var subst: std.StringHashMapUnmanaged(*const Ty) = .empty;
            const is_poly_fn = fsig.type_params.len > 0 or fsig.hkt_params.len > 0;
            if (piped_recv) |pr| {
                if (fsig.params.len > 0) {
                    if (is_poly_fn) {
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
                if (is_poly_fn and expected_p != null) {
                    if (isNumericLiteralExpr(arg.value)) continue;
                    const ep_sub = try self.substituteType(expected_p.?, &subst);
                    const has_free = containsUnresolvedTypeVar(ep_sub, &subst);
                    const ar = try self.checkExpr(arg.value, if (has_free) null else ep_sub);
                    const final_ar_ty = if (has_free)
                        try self.finalizeInferredType(arg.value.getSpan(), ar)
                    else
                        ar.ty;
                    if (ep_sub.* == .view and arg.value.* == .field) {
                        if (self.expr_types.get(arg.value.field.target)) |ft| {
                            if (recordOfType(ft)) |ri| {
                                if (self.findRecordField(ri, arg.value.field.name.slice(self.source))) |fi| {
                                    if (fi < self.record_defs.items[ri].address_taken_fields.len) {
                                        self.record_defs.items[ri].address_taken_fields[fi] = true;
                                    }
                                }
                            }
                        }
                    }
                    if (!ep_sub.isCopyable() and arg.value.* == .ident) {
                        const vname = arg.value.ident.slice(self.source);
                        if (self.lookupVar(vname)) |vb| {
                            if (ep_sub.* != .view and ep_sub.* != .slice and ep_sub.* != .path_borrow) {
                                vb.moved = true;
                            }
                        }
                    }
                    if (expected_p.?.* == .type_var) {
                        const tv = expected_p.?.type_var;
                        if (subst.get(tv)) |bound| {
                            if (bound.* != .err and !bound.eql(final_ar_ty.*)) {
                                if (try self.joinLosslessScalarTy(bound, final_ar_ty)) |joined| {
                                    try subst.put(self.alloc, tv, joined);
                                    continue;
                                }
                            }
                        }
                    }
                    if (!try self.unifyType(expected_p.?, final_ar_ty, &subst)) {
                        self.addError(.type_mismatch, arg.span, "argument does not match generic function type parameter");
                    }
                } else {
                    const ar = try self.checkExpr(arg.value, expected_p);
                    if (expected_p) |ep| {
                        if (ep.* == .view and arg.value.* == .field) {
                            if (self.expr_types.get(arg.value.field.target)) |ft| {
                                if (recordOfType(ft)) |ri| {
                                    if (self.findRecordField(ri, arg.value.field.name.slice(self.source))) |fi| {
                                        if (fi < self.record_defs.items[ri].address_taken_fields.len) {
                                            self.record_defs.items[ri].address_taken_fields[fi] = true;
                                        }
                                    }
                                }
                            }
                        }
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
            if (is_poly_fn) {
                for (args, 0..) |arg, ai| {
                    const param_idx = ai + recv_offset;
                    const expected_p = if (param_idx < fsig.params.len) fsig.params[param_idx] else null;
                    if (expected_p == null) continue;
                    const ep_sub = try self.substituteType(expected_p.?, &subst);
                    if (isNumericLiteralExpr(arg.value)) {
                        const has_free = containsUnresolvedTypeVar(ep_sub, &subst);
                        const ar = try self.checkExpr(arg.value, if (has_free) null else ep_sub);
                        const final_ar_ty = if (has_free)
                            try self.finalizeInferredType(arg.value.getSpan(), ar)
                        else
                            ar.ty;
                        if (expected_p.?.* == .type_var) {
                            const tv = expected_p.?.type_var;
                            if (subst.get(tv)) |bound| {
                                if (bound.* != .err and !bound.eql(final_ar_ty.*)) {
                                    if (try self.joinLosslessScalarTy(bound, final_ar_ty)) |joined| {
                                        try subst.put(self.alloc, tv, joined);
                                        continue;
                                    }
                                }
                            }
                        }
                        if (!try self.unifyType(expected_p.?, final_ar_ty, &subst)) {
                            self.addError(.type_mismatch, arg.span, "argument does not match generic function type parameter");
                        }
                    } else {
                        const ar_ty = self.expr_types.get(arg.value) orelse continue;
                        if (ep_sub.* != .type_var and !ep_sub.eql(ar_ty.*)) {
                            try self.checkAssignmentValue(arg.span, ep_sub, .{ .ty = ar_ty, .range = ar_ty.rangeOf() });
                        }
                    }
                }
            }
            if (is_poly_fn and expected != null and expected.?.* != .err) {
                _ = self.unifyType(fsig.ret, expected.?, &subst) catch false;
            }
            if (fsig.type_params.len > 0) {
                const concrete = try self.alloc.alloc(*const Ty, fsig.type_params.len);
                for (fsig.type_params, 0..) |tp, ti| {
                    concrete[ti] = subst.get(tp) orelse try self.allocTy(.{ .type_var = tp });
                }
                try self.call_type_args.put(self.alloc, call_expr, concrete);
            }
            var resolved_ws: []const ResolvedWitness = &.{};
            if (fsig.constraints.len > 0 or fsig.hkt_params.len > 0) {
                resolved_ws = try self.resolveConstraintsList(fsig.constraints, &subst, span);
                const hkt_concrete = try self.alloc.alloc(?[]const u8, fsig.hkt_params.len);
                for (fsig.hkt_params, 0..) |hp, hi| {
                    const hkey = try std.fmt.allocPrint(self.alloc, "__hkt__{s}", .{hp});
                    hkt_concrete[hi] = if (subst.get(hkey)) |bt| self.hktNameFromTy(bt) else hp;
                }
                const fn_targs = self.call_type_args.get(call_expr) orelse &.{};
                try self.call_trait_resolutions.put(self.alloc, call_expr, .{
                    .kind = .{ .constrained_fn = fsig.name },
                    .witnesses = resolved_ws,
                    .type_args = fn_targs,
                    .hkt_args = hkt_concrete,
                });
            }
            if (fsig.is_extern) {
                try self.checkRustFFISliceAliasing(span, fsig.params, piped_recv_expr, args);
                try self.checkRustFFICallbackArgs(fsig.params, piped_recv_expr, args);
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
            if (piped_recv == null and self.current_fn_name != null and self.current_fn_decreases != null and std.mem.eql(u8, fsig.name, self.current_fn_name.?)) {
                const arg_exprs = try self.alloc.alloc(*const ast.Expr, args.len);
                for (args, 0..) |a, ai| arg_exprs[ai] = a.value;
                try self.verifyRecursiveDecreasesCall(span, arg_exprs);
            }
            const raw_ret = if (fsig.type_params.len > 0 or fsig.hkt_params.len > 0) try self.substituteType(fsig.ret, &subst) else fsig.ret;
            const final_ret = try self.instantiateReturnBrand(raw_ret, resolved_ws);
            return .{ .ty = final_ret, .range = final_ret.rangeOf() };
        }

        if (callee.* == .ident and self.lookupVar(callee.ident.slice(self.source)) == null) {
            if (try self.tryCheckTraitMethodCall(call_expr, span, callee.ident.slice(self.source), args, piped_recv, expected)) |tres| {
                return tres;
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
                if (self.module_slices.len > 0 and adt_def.module_id != self.current_module_id and !adt_def.is_pub) continue;
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

        // Handle qualified constructors `Status.Moving(...)`, `v2.Status.Moving(...)`, `v2.Moving(...)`.
        if (callee.* == .field and callee.field.target.* == .field and callee.field.target.field.target.* == .ident) {
            const mod_alias = callee.field.target.field.target.ident.slice(self.source);
            const adt_name = callee.field.target.field.name.slice(self.source);
            const var_name = callee.field.name.slice(self.source);
            if (self.resolveImportedModule(self.current_module_id, mod_alias)) |target_mod| {
                if (self.findADTInModule(target_mod, adt_name)) |aidx| {
                    if (!self.adt_defs.items[aidx].is_pub and target_mod != self.current_module_id) {
                        self.addError(.visibility_error, callee.field.target.field.name, "ADT type is private in imported module");
                    }
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
                }
            }
        }
        if (callee.* == .field and callee.field.target.* == .ident and self.lookupVar(callee.field.target.ident.slice(self.source)) == null) {
            const mod_alias = callee.field.target.ident.slice(self.source);
            const var_name = callee.field.name.slice(self.source);
            if (self.resolveImportedModule(self.current_module_id, mod_alias)) |target_mod| {
                for (self.adt_defs.items, 0..) |adt_def, aidx| {
                    if (adt_def.module_id != target_mod) continue;
                    for (adt_def.variants) |v| {
                        if (std.mem.eql(u8, v.name, var_name)) {
                            if (!adt_def.is_pub and target_mod != self.current_module_id) {
                                self.addError(.visibility_error, callee.field.name, "ADT variant is private in imported module");
                            }
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
        }
        if (callee.* == .field and callee.field.target.* == .upper_ident) {
            const adt_name = callee.field.target.upper_ident.slice(self.source);
            const var_name = callee.field.name.slice(self.source);
            if (self.resolveVisibleADTIndex(adt_name, callee.field.target.upper_ident)) |aidx| {
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

    fn recordBindingRead(self: *Analyzer, span: ast.Span, binding: *const Binding) std.mem.Allocator.Error!void {
        try self.recordAccess(
            binding.view_root orelse span.slice(self.source),
            binding.view_record_idx orelse recordOfType(binding.ty),
            binding.view_field_idx,
            false,
            span,
            binding.view_index_key,
            binding.view_id,
        );
    }

    fn readIntegerOperand(self: *Analyzer, expr: *const ast.Expr, operand: ExprResult) std.mem.Allocator.Error!ExprResult {
        if (operand.ty.* != .view) return operand;
        const target = operand.ty.view.target;
        if (target.isInteger() == null) return operand;
        if (expr.* == .ident) {
            const binding = self.lookupVar(expr.ident.slice(self.source));
            if (binding != null and binding.?.view_id != null) {
                const captured = if (self.active_fork_start) |start|
                    !self.in_projection_base and binding.?.decl_span.start < start
                else
                    false;
                if (!captured) try self.recordBindingRead(expr.ident, binding.?);
            }
        }
        return .{ .ty = target, .range = target.rangeOf() };
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
                if (lr.ty.* == .f32 or lr.ty.* == .f64 or rr.ty.* == .f32 or rr.ty.* == .f64) {
                    const joined = try self.joinLosslessScalarTy(lr.ty, rr.ty);
                    if (joined == null) {
                        self.addError(.type_mismatch, span, "cannot implicitly mix float with integer exceeding exact float precision; use explicit 'as f32' or 'as f64'");
                        return .{ .ty = try self.allocTy(.err), .range = null };
                    }
                    return .{ .ty = joined.?, .range = null };
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

    fn isTraitDispatchableScalarTarget(ty: *const Ty) bool {
        return switch (ty.*) {
            .type_var, .record, .adt, .applied => true,
            else => false,
        };
    }

    fn resolveNumeralFromInt(
        self: *Analyzer,
        expr: *const ast.Expr,
        span: ast.Span,
        mag: u128,
        negative: bool,
        target_ty: *const Ty,
    ) std.mem.Allocator.Error!?*const Ty {
        const tidx = self.resolveVisibleTraitIndex("FromInt", span) orelse return null;
        const i32_ty = int_range.IntType{ .signed = true, .bits = 32 };
        const fits = if (negative) int_range.fitsSignedNegated(mag, i32_ty) else int_range.fitsNonNeg(mag, i32_ty);
        if (!fits) {
            self.addError(.literal_out_of_range, span, "integer literal exceeds FromInt(i32) range");
            return target_ty;
        }
        if (self.resolveTraitWitness(tidx, &.{target_ty}, &.{null}, span, true)) |w| {
            try self.numeral_trait_resolutions.put(self.alloc, expr, w);
        }
        return target_ty;
    }

    fn resolveNumericTraitByName(
        self: *Analyzer,
        expr: ?*const ast.Expr,
        span: ast.Span,
        trait_name: []const u8,
        method_name: []const u8,
        target_ty: *const Ty,
    ) std.mem.Allocator.Error!?CallTraitResolution {
        const tidx = self.resolveVisibleTraitIndex(trait_name, span) orelse return null;
        const w = self.resolveTraitWitness(tidx, &.{target_ty}, &.{null}, span, true) orelse return null;
        const ctr = CallTraitResolution{
            .kind = .{ .trait_method = .{ .method_name = method_name, .witness = w } },
            .witnesses = &.{},
            .type_args = &.{},
        };
        if (expr) |e| {
            try self.call_trait_resolutions.put(self.alloc, e, ctr);
        }
        return ctr;
    }

    fn resolveNumericOpTrait(
        self: *Analyzer,
        expr: ?*const ast.Expr,
        span: ast.Span,
        op: ast.BinaryOp,
        target_ty: *const Ty,
    ) std.mem.Allocator.Error!?CallTraitResolution {
        return switch (op) {
            .add => try self.resolveNumericTraitByName(expr, span, "Semiring", "add", target_ty),
            .mul => try self.resolveNumericTraitByName(expr, span, "Semiring", "mul", target_ty),
            .sub => try self.resolveNumericTraitByName(expr, span, "Ring", "sub", target_ty),
            .div => try self.resolveNumericTraitByName(expr, span, "Field", "div", target_ty),
            else => null,
        };
    }

    fn isNumericLiteralExpr(expr: *const ast.Expr) bool {
        return switch (expr.*) {
            .int_lit, .float_lit => true,
            .unary => |u| u.op == .neg and (u.operand.* == .int_lit or u.operand.* == .float_lit),
            else => false,
        };
    }

    fn extractPureFieldPath(self: *const Analyzer, expr: *const ast.Expr) ?struct { root: []const u8, field: []const u8 } {
        if (expr.* != .field) return null;
        const fld = expr.field;
        if (fld.target.* != .ident) return null;
        return .{
            .root = fld.target.ident.slice(self.source),
            .field = fld.name.slice(self.source),
        };
    }

    fn lookupFieldRange(self: *const Analyzer, root: []const u8, field: []const u8) ?IntRange {
        var i = self.field_ranges.items.len;
        while (i > 0) {
            i -= 1;
            const entry = self.field_ranges.items[i];
            if (std.mem.eql(u8, entry.root, root) and std.mem.eql(u8, entry.field, field)) {
                return entry.range;
            }
        }
        return null;
    }

    fn setFieldRange(self: *Analyzer, root: []const u8, field: []const u8, rng: IntRange) std.mem.Allocator.Error!void {
        for (self.field_ranges.items) |*entry| {
            if (std.mem.eql(u8, entry.root, root) and std.mem.eql(u8, entry.field, field)) {
                entry.range = rng;
                return;
            }
        }
        try self.field_ranges.append(self.alloc, .{ .root = root, .field = field, .range = rng });
    }

    fn removeFieldRange(self: *Analyzer, root: []const u8, field: []const u8) void {
        var i = self.field_ranges.items.len;
        while (i > 0) {
            i -= 1;
            const entry = self.field_ranges.items[i];
            if (std.mem.eql(u8, entry.root, root) and std.mem.eql(u8, entry.field, field)) {
                _ = self.field_ranges.swapRemove(i);
            }
        }
    }

    fn invalidateRootFieldRanges(self: *Analyzer, root: []const u8) void {
        var i = self.field_ranges.items.len;
        while (i > 0) {
            i -= 1;
            if (std.mem.eql(u8, self.field_ranges.items[i].root, root)) {
                _ = self.field_ranges.swapRemove(i);
            }
        }
    }

    fn resolveFieldBaseRange(self: *Analyzer, root: []const u8, field: []const u8) ?IntRange {
        if (self.lookupFieldRange(root, field)) |fr| return fr;
        const vb = self.lookupVar(root) orelse return null;
        const ridx = recordOfType(vb.ty) orelse return null;
        const fidx = self.findRecordField(ridx, field) orelse return null;
        return self.record_defs.items[ridx].fields[fidx].ty.rangeOf();
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
                } else if (self.extractPureFieldPath(b.left)) |fp| {
                    if (evalConstInt(self.source, b.right)) |bound| {
                        if (self.resolveFieldBaseRange(fp.root, fp.field)) |cur| {
                            if (if (truthy) b.op else invertCmpOp(b.op)) |effective_op| {
                                if (narrowByCmp(cur, effective_op, bound)) |nr| {
                                    try self.setFieldRange(fp.root, fp.field, nr);
                                }
                            }
                        }
                    }
                } else if (self.extractPureFieldPath(b.right)) |fp| {
                    if (evalConstInt(self.source, b.left)) |bound| {
                        if (self.resolveFieldBaseRange(fp.root, fp.field)) |cur| {
                            if (flipCmpOp(b.op)) |flipped| {
                                if (if (truthy) flipped else invertCmpOp(flipped)) |effective_op| {
                                    if (narrowByCmp(cur, effective_op, bound)) |nr| {
                                        try self.setFieldRange(fp.root, fp.field, nr);
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

    fn checkRustFFICallbackArgs(
        self: *Analyzer,
        param_types: []const *const Ty,
        piped_recv_expr: ?*const ast.Expr,
        args: []const ast.CallArg,
    ) std.mem.Allocator.Error!void {
        const recv_offset: usize = if (piped_recv_expr != null) 1 else 0;
        for (param_types, 0..) |pt, pidx| {
            if (pt.* != .fn_ty) continue;
            const actual: *const ast.Expr = if (piped_recv_expr != null and pidx == 0)
                piped_recv_expr.?
            else if (pidx >= recv_offset and (pidx - recv_offset) < args.len)
                args[pidx - recv_offset].value
            else
                continue;

            switch (actual.*) {
                .ident => |sp| {
                    const name = sp.slice(self.source);
                    if (self.lookupVar(name) != null) {
                        self.addError(.invalid_ffi_type, actual.getSpan(), "Aethel -> Rust FFI callback cannot capture local closures; pass a top-level fn or capture-free fn(...)");
                        continue;
                    }
                    if (self.resolved_idents.get(actual) == null and self.resolveCalleeFnIndex(actual, false) == null) {
                        self.addError(.invalid_ffi_type, actual.getSpan(), "Aethel -> Rust FFI callback must reference a top-level function or capture-free fn(...)");
                    }
                },
                .field => {
                    if (self.resolved_idents.get(actual) == null) {
                        self.addError(.invalid_ffi_type, actual.getSpan(), "Aethel -> Rust FFI callback must reference a top-level function or capture-free fn(...)");
                    }
                },
                .lambda => |lam| {
                    var raw_refs: std.ArrayList(FreeVarRef) = .empty;
                    try self.collectFreeRefsBlock(&lam.body, &raw_refs);
                    var has_capture = false;
                    for (raw_refs.items) |r| {
                        var is_param = false;
                        for (lam.params) |lp| {
                            if (std.mem.eql(u8, lp.name.slice(self.source), r.name)) {
                                is_param = true;
                                break;
                            }
                        }
                        if (is_param) continue;
                        if (self.lookupVar(r.name) != null) {
                            has_capture = true;
                            break;
                        }
                    }
                    if (has_capture) {
                        self.addError(.invalid_ffi_type, actual.getSpan(), "Aethel -> Rust FFI callback cannot capture local variables; pass a top-level fn or capture-free fn(...)");
                    }
                },
                else => {
                    self.addError(.invalid_ffi_type, actual.getSpan(), "Aethel -> Rust FFI callback must be a top-level fn reference or capture-free fn(...) lambda");
                },
            }
        }
    }

    fn checkRustFFISliceAliasing(
        self: *Analyzer,
        span: ast.Span,
        param_types: []const *const Ty,
        piped_recv_expr: ?*const ast.Expr,
        args: []const ast.CallArg,
    ) std.mem.Allocator.Error!void {
        const SliceArg = struct {
            is_mut: bool,
            root: ?[]const u8,
            field_idx: ?usize,
            idx_key: ?AccessIndex,
        };
        var items_buf: [16]SliceArg = undefined;
        var items_len: usize = 0;
        const recv_offset: usize = if (piped_recv_expr != null) 1 else 0;

        for (param_types, 0..) |pt, pidx| {
            const is_slice = pt.* == .slice or (pt.* == .view and pt.view.target.* == .slice);
            if (!is_slice) continue;
            const is_mut = switch (pt.*) {
                .slice => |s| s.mutable,
                .view => |v| v.mode == .exclusive and v.target.slice.mutable,
                else => false,
            };
            const actual: *const ast.Expr = if (piped_recv_expr != null and pidx == 0)
                piped_recv_expr.?
            else if (pidx >= recv_offset and (pidx - recv_offset) < args.len)
                args[pidx - recv_offset].value
            else
                continue;

            var resolved: ResolvedRoot = .{};
            var field_idx: ?usize = null;
            var idx_key: ?AccessIndex = null;

            if (actual.* == .index) {
                if (actual.index.target.* == .field) {
                    const fld = actual.index.target.field;
                    resolved = self.resolveAccessRoot(fld.target);
                    if (resolved.root_name) |rn| {
                        if (self.lookupVar(rn)) |vb| {
                            if (recordOfType(vb.ty)) |ri| {
                                field_idx = self.findRecordField(ri, fld.name.slice(self.source));
                            }
                        }
                    }
                } else {
                    resolved = self.resolveAccessRoot(actual.index.target);
                }
                idx_key = resolved.view_index_key orelse self.extractAccessIndex(actual.index.idx);
            } else if (actual.* == .field) {
                resolved = self.resolveAccessRoot(actual.field.target);
                if (resolved.root_name) |rn| {
                    if (self.lookupVar(rn)) |vb| {
                        if (recordOfType(vb.ty)) |ri| {
                            field_idx = self.findRecordField(ri, actual.field.name.slice(self.source));
                        }
                    }
                }
                idx_key = resolved.view_index_key;
            } else {
                resolved = self.resolveAccessRoot(actual);
                idx_key = resolved.view_index_key;
            }

            if (items_len < items_buf.len) {
                items_buf[items_len] = .{
                    .is_mut = is_mut,
                    .root = resolved.root_name,
                    .field_idx = field_idx,
                    .idx_key = idx_key,
                };
                items_len += 1;
            }
        }

        const slice_args = items_buf[0..items_len];
        var i: usize = 0;
        while (i < slice_args.len) : (i += 1) {
            var j: usize = i + 1;
            while (j < slice_args.len) : (j += 1) {
                const a = slice_args[i];
                const b = slice_args[j];
                if (!a.is_mut and !b.is_mut) continue;
                if (a.root == null or b.root == null) continue;
                if (!std.mem.eql(u8, a.root.?, b.root.?)) continue;
                if (a.field_idx != null and b.field_idx != null and a.field_idx.? != b.field_idx.?) {
                    continue;
                }
                if (a.idx_key != null and b.idx_key != null and self.accessIndicesDisjoint(a.idx_key.?, b.idx_key.?, true)) {
                    continue;
                }
                self.addError(.borrow_conflict, span, "Rust FFI call passes overlapping mutable slice aliases (violates Rust &mut aliasing rules)");
            }
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
        const field = self.directReturnedByteField(expr, vb);
        switch (self.inferred_return_field) {
            .pending => self.inferred_return_field = if (field) |precise| .{ .precise = precise } else .whole,
            .precise => |previous| {
                if (field == null or !std.meta.eql(previous, field.?)) self.inferred_return_field = .whole;
            },
            .whole => {},
        }
    }

    fn directReturnedByteField(self: *Analyzer, expr: *const ast.Expr, binding: *const Binding) ?ParamFieldEffect {
        if (!binding.is_param or expr.* != .field or expr.field.target.* != .ident) return null;
        const param = binding.param_index orelse return null;
        const record = recordOfType(binding.ty) orelse return null;
        const field = self.findRecordField(record, expr.field.name.slice(self.source)) orelse return null;
        const ty = self.record_defs.items[record].fields[field].ty;
        if (ty.* != .int or ty.int.signed or ty.int.bits != 8) return null;
        if (binding.authorized_paths) |paths| {
            if (std.mem.indexOfScalar(usize, paths, field) == null) {
                self.addError(.unauthorized_field_access, expr.field.name, "returned field is outside the parameter path borrow contract");
                return null;
            }
        }
        return .{ .param_idx = param, .record_idx = record, .field_idx = field };
    }

    fn returnedFieldOnArgument(self: *Analyzer, field: ?ParamFieldEffect, arg: *const ast.Expr) ?ParamFieldEffect {
        const precise = field orelse return null;
        if (arg.* != .ident) return null;
        const binding = self.lookupVar(arg.ident.slice(self.source)) orelse return null;
        if (binding.view_root != null or recordOfType(binding.ty) != precise.record_idx) return null;
        return precise;
    }

    fn attachReturnedViewBinding(
        self: *Analyzer,
        vb: *Binding,
        val_expr: *const ast.Expr,
        vty: anytype,
        span: ast.Span,
    ) std.mem.Allocator.Error!void {
        if (val_expr.* == .call) {
            if (self.resolveCalleeFnIndex(val_expr.call.callee, false)) |fidx| {
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
                        const field = self.returnedFieldOnArgument(fsig.returned_field, arg_expr);
                        const ridx = if (field) |precise| precise.record_idx else vty.target_record;
                        const field_idx = if (field) |precise| precise.field_idx else null;

                        for (self.active_views.items) |av| {
                            if (!av.active) continue;
                            if (std.mem.eql(u8, av.root_name, root_name) and root_name.len > 0) {
                                if (av.index_key != null and idx_key != null) {
                                    if (self.accessIndicesDisjoint(av.index_key.?, idx_key.?, true)) continue;
                                }
                                if (fieldsMayOverlap(av.field_idx, field_idx) and !BorrowPerm.compatible(init_perm, av.perm)) {
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
                                .field_idx = field_idx,
                                .perm = init_perm,
                            } });
                        }
                        try self.active_views.append(self.alloc, .{
                            .id = vid,
                            .binding_name = vb.name,
                            .root_name = root_name,
                            .record_idx = ridx,
                            .field_idx = field_idx,
                            .index_key = idx_key,
                            .perm = init_perm,
                            .active = true,
                            .is_sentinel = false,
                            .in_trace = in_trace,
                        });
                        vb.view_id = vid;
                        vb.view_root = if (root_name.len > 0) root_name else null;
                        vb.view_record_idx = ridx;
                        vb.view_field_idx = field_idx;
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
            if (is_write) self.invalidateRootFieldRanges(rn);
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
            self.current_module_id = self.moduleIdOfSpan(decl.span);
            if (decl.kind != .fn_decl) continue;
            const fd = decl.kind.fn_decl;
            const fidx = self.findFnInModule(self.current_module_id, fd.name.slice(self.source)) orelse self.findFnIndex(fd.name.slice(self.source)) orelse continue;

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
                if (self.resolveCalleeFnIndex(c.callee, false)) |callee_idx| {
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

    fn isSimdCmpOp(op: ast.BinaryOp) bool {
        return switch (op) {
            .eq, .ne, .lt, .le, .gt, .ge => true,
            else => false,
        };
    }

    fn isSimdCmpExpr(self: *const Analyzer, ridx: usize, elem_param: []const u8, cond: *const ast.Expr) bool {
        if (cond.* != .binary) return false;
        const b = cond.binary;
        if (!isSimdCmpOp(b.op)) return false;
        return self.isSimdVectorExpr(ridx, elem_param, b.left) and
            self.isSimdVectorExpr(ridx, elem_param, b.right);
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
            .if_expr => |ie| blk: {
                const eb = ie.else_branch orelse break :blk false;
                if (eb.* != .block) break :blk false;
                if (ie.then_block.stmts.len != 0 or ie.then_block.tail == null) break :blk false;
                if (eb.block.stmts.len != 0 or eb.block.tail == null) break :blk false;
                break :blk self.isSimdCmpExpr(ridx, elem_param, ie.cond) and
                    self.isSimdVectorExpr(ridx, elem_param, ie.then_block.tail.?) and
                    self.isSimdVectorExpr(ridx, elem_param, eb.block.tail.?);
            },
            .cast => |c| self.isSimdVectorExpr(ridx, elem_param, c.expr),
            else => false,
        };
    }

    fn isSimdAssignStmt(self: *const Analyzer, ridx: usize, elem_param: []const u8, st: ast.Stmt, allow_ident_target: bool) ?bool {
        if (st != .assign_stmt) return null;
        const asg = st.assign_stmt;
        switch (asg.op) {
            .assign, .add_assign, .sub_assign, .mul_assign, .div_assign => {},
            else => return null,
        }
        if (!self.isSimdVectorExpr(ridx, elem_param, asg.value)) return null;
        if (asg.target.* == .field) {
            const fld = asg.target.field;
            if (fld.target.* != .ident) return null;
            if (!std.mem.eql(u8, fld.target.ident.slice(self.source), elem_param)) return null;
            const fi = self.findRecordField(ridx, fld.name.slice(self.source)) orelse return null;
            if (!isSimdFieldTy(self.record_defs.items[ridx].fields[fi].ty)) return null;
            return true;
        }
        if (allow_ident_target and asg.target.* == .ident) return false;
        return null;
    }

    fn isSimdIfExpr(self: *const Analyzer, ridx: usize, elem_param: []const u8, ie: anytype) ?bool {
        if (!self.isSimdCmpExpr(ridx, elem_param, ie.cond)) return null;
        if (ie.then_block.tail != null or ie.then_block.stmts.len == 0) return null;
        var has_field_write = false;
        for (ie.then_block.stmts) |tst| {
            const wf = self.isSimdAssignStmt(ridx, elem_param, tst, false) orelse return null;
            if (wf) has_field_write = true;
        }
        if (ie.else_branch) |eb| {
            if (eb.* != .block or eb.block.tail != null or eb.block.stmts.len == 0) return null;
            for (eb.block.stmts) |est| {
                const wf = self.isSimdAssignStmt(ridx, elem_param, est, false) orelse return null;
                if (wf) has_field_write = true;
            }
        }
        return has_field_write;
    }

    fn isSimdVectorizableLambda(self: *const Analyzer, ridx: usize, elem_param: []const u8, body: *const ast.Block) bool {
        if (body.stmts.len == 0 and body.tail == null) return false;
        var has_field_write = false;
        for (body.stmts) |st| {
            switch (st) {
                .let_stmt => |ls| {
                    if (ls.pattern.* != .ident) return false;
                    if (!self.isSimdVectorExpr(ridx, elem_param, ls.value)) return false;
                },
                .assign_stmt => {
                    const wf = self.isSimdAssignStmt(ridx, elem_param, st, true) orelse return false;
                    if (wf) has_field_write = true;
                },
                .expr_stmt => |es| {
                    if (es.expr.* != .if_expr) return false;
                    const wf = self.isSimdIfExpr(ridx, elem_param, es.expr.if_expr) orelse return false;
                    if (wf) has_field_write = true;
                },
                else => return false,
            }
        }
        if (body.tail) |tail| {
            if (tail.* != .if_expr) return false;
            const wf = self.isSimdIfExpr(ridx, elem_param, tail.if_expr) orelse return false;
            if (wf) has_field_write = true;
        }
        return has_field_write;
    }

    fn synthesizeRecordLayout(
        self: *Analyzer,
        ridx: usize,
        computed: []bool,
        in_progress: []bool,
        out: []CheckedRecord,
    ) std.mem.Allocator.Error!void {
        if (computed[ridx]) return;
        if (in_progress[ridx]) return;
        in_progress[ridx] = true;
        const rdef = &self.record_defs.items[ridx];
        const schemas = try self.alloc.alloc(layout.FieldSchema, rdef.fields.len);
        for (rdef.fields, 0..) |f, fi| {
            var info = self.typeBitInfo(f.ty);
            if (f.ty.* == .record) {
                const inner_ri = f.ty.record;
                if (inner_ri < self.record_defs.items.len and !in_progress[inner_ri]) {
                    try self.synthesizeRecordLayout(inner_ri, computed, in_progress, out);
                    if (computed[inner_ri]) {
                        const inner_rl = out[inner_ri].record_layout;
                        info.size = inner_rl.size;
                        info.alignment = inner_rl.alignment;
                        info.bits = @min(@as(u16, 65535), @as(u16, @intCast(inner_rl.size * 8)));
                        info.packable = false;
                    }
                }
            }
            const addr_taken = fi < rdef.address_taken_fields.len and rdef.address_taken_fields[fi];
            schemas[fi] = .{
                .name = f.name,
                .bits = @max(@as(u16, 1), info.bits),
                .signed = info.signed,
                .addressable_size = info.size,
                .addressable_align = info.alignment,
                .is_packable = info.packable and !addr_taken and rdef.type_params.len == 0,
            };
        }
        const base_naive = if (rdef.is_flat_c)
            try layout.planFlatCLayout(self.alloc, schemas)
        else
            try layout.planRecordLayout(self.alloc, schemas, rdef.conflicts.items);
        var unpacked_any = false;
        if (rdef.auto_layout_requested and !rdef.is_flat_c) {
            for (schemas, 0..) |*sc, fi| {
                if (sc.is_packable and fi < rdef.hot_fields.len and
                    layout.shouldUnpackHotInL1(rdef.hot_fields[fi], rdef.observed_collection_len, base_naive.size))
                {
                    sc.is_packable = false;
                    unpacked_any = true;
                }
            }
        }
        const base_planned = if (rdef.is_flat_c or !unpacked_any)
            base_naive
        else
            try layout.planRecordLayout(self.alloc, schemas, rdef.conflicts.items);

        var hot_count: usize = 0;
        var hot_bytes: usize = 0;
        if (!rdef.is_flat_c) {
            for (rdef.hot_fields, 0..) |is_h, fi| {
                if (is_h) {
                    hot_count += 1;
                    hot_bytes += @max(@as(usize, 1), schemas[fi].addressable_size);
                }
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
        if (!rdef.is_flat_c and hot_count > 0 and hot_count < rdef.fields.len and rdef.fields.len > 1) {
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

        if (rdef.has_pod_derive) {
            var sum_sizes: usize = 0;
            var all_pod_safe = rdef.fields.len > 0;
            for (rdef.fields, 0..) |f, fi| {
                sum_sizes += schemas[fi].addressable_size;
                if (!self.isPodBitPatternSafeTy(f.ty, 0)) {
                    all_pod_safe = false;
                }
            }
            if (!all_pod_safe or sum_sizes != final_planned.size) {
                self.addError(.invalid_ffi_type, rdef.span, "@derive(rust, \"bytemuck::Pod\") requires non-empty @layout(flat) record with zero implicit padding and no bool/@opaque fields");
            }
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
            .is_flat_c = rdef.is_flat_c,
            .rust_derives = rdef.rust_derives,
            .rust_attrs = rdef.rust_attrs,
            .has_pod_derive = rdef.has_pod_derive,
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
        if (rdef.used_in_dyn_vec) {
            try self.checked_dyn_vecs.append(self.alloc, .{
                .name = rdef.name,
                .layout = rdef.collection_layout orelse .aos,
                .field_count = @max(@as(usize, 1), rdef.fields.len),
            });
        }
        in_progress[ridx] = false;
        computed[ridx] = true;
    }

    fn synthesizeAllLayouts(self: *Analyzer) std.mem.Allocator.Error![]CheckedRecord {
        const out = try self.alloc.alloc(CheckedRecord, self.record_defs.items.len);
        const computed = try self.alloc.alloc(bool, self.record_defs.items.len);
        const in_progress = try self.alloc.alloc(bool, self.record_defs.items.len);
        @memset(computed, false);
        @memset(in_progress, false);
        for (0..self.record_defs.items.len) |ridx| {
            try self.synthesizeRecordLayout(ridx, computed, in_progress, out);
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
                if (!fd.has_body) continue;
                const cname = self.decl_canonical_names.get(decl.span.start) orelse fd.name.slice(self.source);
                try list.append(self.alloc, .{
                    .name = cname,
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

    fn isLawByte(ty: *const Ty) bool {
        return ty.* == .int and !ty.int.signed and ty.int.bits == 8;
    }

    fn tyToParamDomain(self: *const Analyzer, name: []const u8, ty: *const Ty) std.mem.Allocator.Error!law_verifier.LawParamDomain {
        const inner = if (ty.* == .view) ty.view.target else ty;
        switch (inner.*) {
            .bool => return .{ .name = name, .kind = .bool_ty },
            .int => |it| return .{ .name = name, .kind = .{ .int_ty = .{ .int_ty = it, .range = inner.rangeOf() } } },
            .int_range => |ir| return .{ .name = name, .kind = .{ .int_ty = .{ .int_ty = ir.synthesized, .range = ir.range } } },
            .option => |payload| {
                const domain = try self.alloc.create(law_verifier.LawParamDomain);
                domain.* = try self.tyToParamDomain(name, payload);
                return .{ .name = name, .kind = .{ .option_ty = domain } };
            },
            .fn_ty => |ft| {
                if (ft.params.len == 1 and isLawByte(ft.params[0])) {
                    if (isLawByte(ft.ret)) return .{ .name = name, .kind = .fn_scalar_ty };
                    if (ft.ret.* == .option and isLawByte(ft.ret.option)) return .{ .name = name, .kind = .fn_opt_ty };
                }
                return .{ .name = name, .kind = .other };
            },
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
        if (self.expr_types.get(dec)) |ty| {
            if (ty.* == .int and !ty.int.signed and ty.int.bits == 8) {
                if (law_verifier.byteFieldCountdown(self.alloc, self.source, cond, dec, body)) |cert| {
                    if (self.current_decreases_certs) |list| try list.append(self.alloc, cert);
                    return;
                }
            }
        }
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

    fn checkFrame(self: *Analyzer, paths: []const ast.FieldPath, span: ast.Span) !?[]const u8 {
        if (paths.len == 0) {
            const msg = "preserves requires a record parameter and field";
            self.addError(.law_violation, span, msg);
            return msg;
        }
        var failure: ?[]const u8 = null;
        for (paths) |fp| {
            const msg: ?[]const u8 = check: {
                if (fp.len != 2) break :check "preserves requires a direct field path of the form parameter.field";
                const vb = self.lookupVar(fp[0].slice(self.source)) orelse break :check "unknown parameter in preserves path";
                const ridx = recordOfType(vb.ty) orelse break :check "preserves path requires a record parameter";
                const fidx = self.findRecordField(ridx, fp[1].slice(self.source)) orelse break :check "preserved field does not exist on record";
                for (self.checked_functions.items) |*cf| {
                    for (cf.writes) |w| {
                        if (w.record_idx == ridx and w.field_idx == fidx)
                            break :check "constitutional law violation: function mutates preserved field";
                    }
                    if (cf.target_record != ridx or std.mem.indexOfScalar(usize, cf.preserves, fidx) != null) continue;
                    const fields = try self.alloc.alloc(usize, cf.preserves.len + 1);
                    @memcpy(fields[0..cf.preserves.len], cf.preserves);
                    fields[cf.preserves.len] = fidx;
                    cf.preserves = fields;
                }
                break :check null;
            };
            if (msg) |reason| {
                self.addError(.law_violation, if (fp.len == 0) span else ast.Span.merge(fp[0], fp[fp.len - 1]), reason);
                if (failure == null) failure = reason;
            }
        }
        return failure;
    }

    fn finishLaw(self: *Analyzer, name: []const u8, span: ast.Span, clauses: []CheckedLawClause, certs: []const law_verifier.SymbolicLawCert) !void {
        var verdict: ?LawVerdict = null;
        var detail: []const u8 = "law has no claims";
        var first_witness: ?[]const u8 = null;
        var mixed = false;
        for (clauses) |cl| {
            const v = cl.verdict orelse continue;
            if (verdict != null and verdict.? != v) mixed = true;
            if (first_witness == null) first_witness = cl.counterexample;
            if (verdict == null or lawVerdictPriority(v) > lawVerdictPriority(verdict.?)) {
                verdict = v;
                detail = cl.detail;
            }
        }
        if (mixed and lawVerdictPriority(verdict.?) < lawVerdictPriority(.unverified_symbolic))
            detail = "proved by multiple methods (see clauses)";
        try self.checked_laws.append(self.alloc, .{
            .name = name,
            .span = span,
            .clauses = clauses,
            .verdict = verdict orelse .unverified_symbolic,
            .tier_detail = detail,
            .counterexample = first_witness,
            .symbolic_certs = certs,
        });
    }

    fn lawVerdictPriority(verdict: LawVerdict) u8 {
        return switch (verdict) {
            .falsified => 7,
            .violated => 6,
            .unverified_symbolic => 5,
            .proved_tier3_lean => 4,
            .proved_tier2_symbolic => 3,
            .proved_tier1_exhaustive => 2,
            .proved_interval => 1,
            .proved_tier0 => 0,
        };
    }

    fn checkLaws(self: *Analyzer, checked_records: []const CheckedRecord) std.mem.Allocator.Error!void {
        _ = checked_records;
        const fn_asts = try self.collectModuleFnAsts();
        const rec_infos = try self.collectRecordAstInfos();

        for (self.module.decls) |decl| {
            self.current_module_id = self.moduleIdOfSpan(decl.span);
            if (decl.kind != .law_decl) continue;
            const ld = decl.kind.law_decl;
            const lname = ld.name.slice(self.source);

            try self.pushScope();
            defer self.popScope();

            var param_domains = try self.alloc.alloc(law_verifier.LawParamDomain, ld.params.len);
            for (ld.params, 0..) |p, pi| {
                const pty = if (p.ty) |t| try self.resolveType(t) else try self.allocTy(.err);
                const pname = p.name.slice(self.source);
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
                .expr_types = &self.expr_types,
                .resolved_calls = &self.resolved_fn_calls,
            };
            for (sym_bindings) |sb| _ = sym_ctx.bindVar(sb.name, sb.non_negative);

            var guards_ast: std.ArrayList(*const ast.Expr) = .empty;
            var sym_certs: std.ArrayList(law_verifier.SymbolicLawCert) = .empty;
            var has_symbolic_guard = false;
            const clauses = try self.alloc.alloc(CheckedLawClause, ld.clauses.len);

            self.field_ranges.clearRetainingCapacity();
            for (ld.clauses, 0..) |cl, ci| {
                const evidence = &clauses[ci];
                evidence.* = CheckedLawClause.init(cl);
                switch (cl) {
                    .preserves => |pr| {
                        if (try self.checkFrame(pr.paths, pr.span)) |reason| {
                            evidence.verdict = .violated;
                            evidence.detail = reason;
                        } else {
                            evidence.verdict = .proved_tier0;
                            evidence.detail = "Tier 0 (structural frame)";
                        }
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
                            evidence.verdict = .proved_interval;
                            evidence.detail = "Tier 2 (interval bounds)";
                            continue;
                        }

                        if (law_verifier.tryProveSymbolicClause(self.alloc, &sym_ctx, guards_ast.items, goal_expr, is_never)) |sym_ok| {
                            evidence.verdict = .proved_tier2_symbolic;
                            evidence.detail = "Tier 2 (symbolic auto-prover)";
                            const cert_name = if (ld.clauses.len <= 1)
                                lname
                            else
                                try std.fmt.allocPrint(self.alloc, "{s}__c{d}", .{ lname, ci });
                            evidence.certificate = cert_name;
                            try sym_certs.append(self.alloc, .{
                                .name = cert_name,
                                .kind = if (is_never) .never else .always,
                                .hyps = sym_ok.hyps,
                                .goal = sym_ok.goal,
                            });
                            continue;
                        }

                        switch (law_verifier.runTier1ClauseResolved(self.alloc, self.source, fn_asts, rec_infos, &self.resolved_fn_calls, param_domains, guards_ast.items, goal_expr, is_never, &self.expr_types)) {
                            .proved_exhaustive => |states| {
                                evidence.verdict = .proved_tier1_exhaustive;
                                evidence.detail = try std.fmt.allocPrint(self.alloc, "Tier 1 (exhaustive, {d} states)", .{states});
                            },
                            .falsified => |witness| {
                                evidence.verdict = .falsified;
                                evidence.counterexample = witness;
                                evidence.detail = witness;
                                const msg = try std.fmt.allocPrint(self.alloc, "constitutional law '{s}' falsified at {s}", .{ lname, witness });
                                self.addError(.law_violation, cl_span, msg);
                            },
                            .inconclusive => {
                                const interval_violated = (is_never and (itruth == .always_true or itruth == .can_fail)) or
                                    (!is_never and (itruth == .always_false or itruth == .can_fail));
                                if (interval_violated) {
                                    evidence.verdict = .violated;
                                    evidence.detail = "constitutional law violated over possible input intervals";
                                    self.addError(.law_violation, cl_span, "constitutional law violated over possible input intervals");
                                }
                            },
                        }
                    },
                }
            }

            try self.finishLaw(lname, decl.span, clauses, try sym_certs.toOwnedSlice(self.alloc));
        }

        try self.checkInstanceLaws(fn_asts, rec_infos);
    }

    fn checkInstanceLaws(
        self: *Analyzer,
        mod_fns: []const law_verifier.FnAstEntry,
        rec_infos: []const law_verifier.RecordAstInfo,
    ) std.mem.Allocator.Error!void {
        const dummy2 = try self.alloc.alloc(ast.Param, 2);
        @memset(dummy2, ast.Param{ .span = .{ .start = 0, .end = 0 }, .label = null, .mutable = false, .name = .{ .start = 0, .end = 0 }, .ty = null });
        const empty_blk = ast.Block{ .span = .{ .start = 0, .end = 0 }, .attrs = &.{}, .stmts = &.{}, .tail = null };

        for (self.instance_defs.items) |inst| {
            if (inst.is_external_rust or inst.type_params.len > 0) {
                var required: std.ArrayList(TraitLawDef) = .empty;
                try self.collectTraitAndSuperLaws(inst.trait_idx, &required);
                for (required.items) |entry| {
                    const name = try std.fmt.allocPrint(self.alloc, "{s}.{s}", .{ inst.name, entry.law.name.slice(self.source) });
                    const clauses = try self.alloc.alloc(CheckedLawClause, entry.law.clauses.len);
                    for (entry.law.clauses, clauses) |clause, *evidence| evidence.* = CheckedLawClause.init(clause);
                    try self.finishLaw(name, inst.span, clauses, &.{});
                }
                continue;
            }

            var inst_fns: std.ArrayList(law_verifier.FnAstEntry) = .empty;
            for (inst.methods) |cm| {
                if (cm.ast_method) |im| {
                    try inst_fns.append(self.alloc, .{
                        .name = cm.local_name,
                        .params = im.params,
                        .body = im.body,
                        .synth = cm.synth,
                    });
                } else if (cm.synth != .none) {
                    try inst_fns.append(self.alloc, .{
                        .name = cm.local_name,
                        .params = dummy2,
                        .body = empty_blk,
                        .synth = cm.synth,
                    });
                }
            }
            for (mod_fns) |mf| try inst_fns.append(self.alloc, mf);
            const all_fns = try inst_fns.toOwnedSlice(self.alloc);

            var all_laws: std.ArrayList(TraitLawDef) = .empty;
            try self.collectTraitAndSuperLaws(inst.trait_idx, &all_laws);
            const subst = try self.buildTraitSubstMap(inst.trait_idx, inst.target_tys, inst.target_hkt_names);

            const tdef_main = self.trait_defs.items[inst.trait_idx];
            const hkt_mark = self.active_hkt_params.items.len;
            for (tdef_main.params) |tp| {
                if (tp.arity >= 1) try self.active_hkt_params.append(self.alloc, tp.name);
            }
            defer self.active_hkt_params.shrinkRetainingCapacity(hkt_mark);

            for (all_laws.items) |tlw| {
                const lw = tlw.law;
                const lname = try std.fmt.allocPrint(self.alloc, "{s}.{s}", .{ inst.name, lw.name.slice(self.source) });
                var param_domains = try self.alloc.alloc(law_verifier.LawParamDomain, lw.params.len);
                var sym_ctx = law_verifier.SymCtx{
                    .alloc = self.alloc,
                    .source = self.source,
                    .fns = all_fns,
                    .resolved_calls = null,
                };
                for (lw.params, 0..) |p, pi| {
                    const raw_pty = if (p.ty) |t| try self.resolveType(t) else try self.allocTy(.err);
                    const sub_pty = try self.substituteType(raw_pty, &subst);
                    const pname = p.name.slice(self.source);
                    param_domains[pi] = try self.tyToParamDomain(pname, sub_pty);
                    const nn = if (isTyNonNegativeNat(sub_pty)) |nni| nni.non_neg else false;
                    _ = sym_ctx.bindVar(pname, nn);
                }

                var guards_ast: std.ArrayList(*const ast.Expr) = .empty;
                var sym_certs: std.ArrayList(law_verifier.SymbolicLawCert) = .empty;
                const clauses = try self.alloc.alloc(CheckedLawClause, lw.clauses.len);

                for (lw.clauses, 0..) |cl, ci| {
                    const evidence = &clauses[ci];
                    evidence.* = CheckedLawClause.init(cl);
                    switch (cl) {
                        .when => |wh| try guards_ast.append(self.alloc, wh.expr),
                        .always, .never, .expr => {
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
                            if (law_verifier.tryProveSymbolicClause(self.alloc, &sym_ctx, guards_ast.items, goal_expr, is_never)) |sym_ok| {
                                evidence.verdict = .proved_tier2_symbolic;
                                evidence.detail = "Tier 2 (symbolic auto-prover)";
                                const cert_name = if (lw.clauses.len <= 1)
                                    lname
                                else
                                    try std.fmt.allocPrint(self.alloc, "{s}__c{d}", .{ lname, ci });
                                evidence.certificate = cert_name;
                                try sym_certs.append(self.alloc, .{
                                    .name = cert_name,
                                    .kind = if (is_never) .never else .always,
                                    .hyps = sym_ok.hyps,
                                    .goal = sym_ok.goal,
                                    .is_trait_law = true,
                                });
                                continue;
                            }
                            switch (law_verifier.runTier1ClauseResolved(self.alloc, self.source, all_fns, rec_infos, null, param_domains, guards_ast.items, goal_expr, is_never, &self.expr_types)) {
                                .proved_exhaustive => |states| {
                                    evidence.verdict = .proved_tier1_exhaustive;
                                    evidence.detail = try std.fmt.allocPrint(self.alloc, "Tier 1 (exhaustive, {d} states)", .{states});
                                },
                                .falsified => |witness| {
                                    evidence.verdict = .falsified;
                                    evidence.counterexample = witness;
                                    evidence.detail = witness;
                                    const msg = try std.fmt.allocPrint(self.alloc, "instance '{s}' violates trait law '{s}' at {s}", .{ inst.local_name, lw.name.slice(self.source), witness });
                                    self.addError(.law_violation, inst.span, msg);
                                    _ = cl_span;
                                },
                                .inconclusive => {},
                            }
                        },
                        .preserves => {
                            evidence.detail = "trait instance preserves checking is unsupported";
                        },
                    }
                }

                try self.finishLaw(lname, inst.span, clauses, try sym_certs.toOwnedSlice(self.alloc));
            }
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
/// on a single parsed `ast.Ast`.
fn isIntegerPattern(pattern: *const ast.Pattern) bool {
    return switch (pattern.*) {
        .literal => |literal| literal.tok.tag == .int_literal,
        .range => |range| isIntegerPattern(range.lo) and isIntegerPattern(range.hi),
        .or_pat => |alternatives| blk: {
            for (alternatives.alternatives) |p| {
                if (isIntegerPattern(p)) break :blk true;
            }
            break :blk false;
        },
        else => false,
    };
}

pub fn hasIntegerPattern(arms: []const ast.CaseArm, subject: usize) bool {
    for (arms) |arm| {
        for (arm.alternatives) |row| {
            if (subject < row.len and isIntegerPattern(row[subject])) return true;
        }
    }
    return false;
}

pub fn analyze(allocator: std.mem.Allocator, tree: *const ast.Ast) std.mem.Allocator.Error!CheckedModule {
    return analyzeWithModules(allocator, tree, &.{}, 0);
}

/// Run full semantic analysis across a multi-file program loaded via `module_loader`.
pub fn analyzeWithModules(
    allocator: std.mem.Allocator,
    tree: *const ast.Ast,
    modules: []const ModuleSliceInfo,
    entry_module_id: usize,
) std.mem.Allocator.Error!CheckedModule {
    return analyzeWithModulesAndManifest(allocator, tree, modules, entry_module_id, null, null);
}

/// Run full semantic analysis with optional Cargo project manifest package name and declared crates.
pub fn analyzeWithModulesAndManifest(
    allocator: std.mem.Allocator,
    tree: *const ast.Ast,
    modules: []const ModuleSliceInfo,
    entry_module_id: usize,
    project_pkg_name: ?[]const u8,
    declared_rust_crates: ?[]const []const u8,
) std.mem.Allocator.Error!CheckedModule {
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
        .opaque_defs = .empty,
        .type_alias_entries = .empty,
        .type_aliases = .empty,
        .fn_sigs = .empty,
        .const_map = .empty,
        .module_slices = modules,
        .entry_module_id = entry_module_id,
        .current_module_id = entry_module_id,
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
        .project_pkg_name = project_pkg_name,
        .declared_rust_crates = declared_rust_crates,
    };

    try az.registerImports();
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

    const checked_traits = try alloc.alloc(CheckedTrait, az.trait_defs.items.len);
    for (az.trait_defs.items, 0..) |t, ti| {
        const cmethods = try alloc.alloc(CheckedTraitMethod, t.methods.len);
        for (t.methods, 0..) |m, mi| {
            cmethods[mi] = .{ .name = m.name, .params = m.params, .ret = m.ret };
        }
        const claws = try alloc.alloc(CheckedTraitLaw, t.laws.len);
        for (t.laws, 0..) |lw, li| {
            claws[li] = .{ .name = lw.name.slice(tree.source), .span = lw.span };
        }
        checked_traits[ti] = .{
            .name = t.name,
            .local_name = t.local_name,
            .params = t.params,
            .supers = t.supers,
            .methods = cmethods,
            .laws = claws,
        };
    }

    const checked_instances = try alloc.alloc(CheckedInstance, az.instance_defs.items.len);
    for (az.instance_defs.items, 0..) |id, ii| {
        checked_instances[ii] = .{
            .name = id.name,
            .local_name = id.local_name,
            .module_id = id.module_id,
            .is_pub = id.is_pub,
            .is_default = id.is_default,
            .is_external_rust = id.is_external_rust,
            .rust_target = id.rust_target,
            .rust_sym = id.rust_sym,
            .trait_idx = id.trait_idx,
            .target_tys = id.target_tys,
            .target_hkt_names = id.target_hkt_names,
            .type_params = id.type_params,
            .hkt_params = id.hkt_params,
            .constraints = id.constraints,
            .methods = id.methods,
            .span = id.span,
        };
    }

    return .{
        .arena = arena,
        .source = tree.source,
        .records = records,
        .adts = adts,
        .collections = try az.checked_collections.toOwnedSlice(alloc),
        .dyn_vecs = try az.checked_dyn_vecs.toOwnedSlice(alloc),
        .functions = try az.checked_functions.toOwnedSlice(alloc),
        .laws = try az.checked_laws.toOwnedSlice(alloc),
        .diagnostics = try diagnostics.toOwnedSlice(alloc),
        .expr_types = az.expr_types,
        .let_types = az.let_types,
        .const_types = az.const_types,
        .call_type_args = az.call_type_args,
        .decl_canonical_names = az.decl_canonical_names,
        .resolved_fn_calls = az.resolved_fn_calls,
        .resolved_idents = az.resolved_idents,
        .resolved_records = az.resolved_records,
        .alias_types = az.type_aliases,
        .traits = checked_traits,
        .instances = checked_instances,
        .foreign_contracts = try az.foreign_contracts.toOwnedSlice(alloc),
        .type_decl_params = az.type_decl_params,
        .call_trait_resolutions = az.call_trait_resolutions,
        .numeral_trait_resolutions = az.numeral_trait_resolutions,
        .assign_trait_resolutions = az.assign_trait_resolutions,
        .std_intrinsic_calls = az.std_intrinsic_calls,
    };
}
