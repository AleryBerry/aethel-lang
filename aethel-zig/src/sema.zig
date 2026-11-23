const std = @import("std");
const lexer = @import("lexer.zig");
const ast = @import("ast.zig");
const int_range = @import("int_range.zig");
const layout = @import("layout.zig");

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
            .fn_ty => true,
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

pub const CheckedFunction = struct {
    name: []const u8,
    span: ast.Span,
    param_types: []const *const Ty,
    ret_type: *const Ty,
    reads: []const FieldAccessEffect,
    writes: []const FieldAccessEffect,
    preserves: []const usize,
    target_record: ?usize,
    has_extern_abi: bool,
};

pub const LawVerdict = enum {
    proved_tier0,
    proved_interval,
    unverified_symbolic,
    violated,
};

pub const CheckedLaw = struct {
    name: []const u8,
    span: ast.Span,
    verdict: LawVerdict,
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
};

const FnSig = struct {
    name: []const u8,
    span: ast.Span,
    params: []const *const Ty,
    param_auths: []const ?[]const usize,
    ret: *const Ty,
    target_record: ?usize,
    is_extern: bool,
    decl_index: ?usize,
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
};

const ActiveView = struct {
    root_name: []const u8,
    record_idx: ?usize,
    field_idx: ?usize,
    mode: ast.BorrowMode,
};

const AccessRecord = struct {
    root_name: []const u8,
    record_idx: ?usize,
    field_idx: ?usize,
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
    current_accesses: ?*std.ArrayList(AccessRecord),

    checked_collections: std.ArrayList(CheckedCollection),
    checked_functions: std.ArrayList(CheckedFunction),
    checked_laws: std.ArrayList(CheckedLaw),

    expr_types: std.AutoHashMapUnmanaged(*const ast.Expr, *const Ty),
    let_types: std.AutoHashMapUnmanaged(usize, *const Ty),
    const_types: std.StringHashMapUnmanaged(*const Ty),
    current_fn_ret: ?*const Ty,

    const RecordDef = struct {
        name: []const u8,
        span: ast.Span,
        fields: []CheckedField,
        conflicts: std.ArrayList(layout.ConflictPair),
        collection_layout: ?layout.CollectionLayout,
        decl_ast: ast.Decl.Kind,
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
    }

    fn popScope(self: *Analyzer) void {
        if (self.scope_marks.pop()) |mark| {
            self.scopes.shrinkRetainingCapacity(mark);
        }
        if (self.view_marks.pop()) |vmark| {
            self.active_views.shrinkRetainingCapacity(vmark);
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
                            for (decl.attrs) |attr| {
                                if (attr.payload == .layout) {
                                    col_lay = try self.resolveLayoutAttr(attr.span, attr.payload.layout);
                                }
                            }
                            const fslice = try self.alloc.alloc(CheckedField, fields.len);
                            try self.record_defs.append(self.alloc, .{
                                .name = name,
                                .span = decl.span,
                                .fields = fslice,
                                .conflicts = .empty,
                                .collection_layout = col_lay,
                                .decl_ast = decl.kind,
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
            .@"packed" => null,
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
                    try self.fn_sigs.append(self.alloc, .{
                        .name = name,
                        .span = fd.name,
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
                return try self.allocTy(.{ .fn_ty = .{ .params = ps, .ret = ret } });
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
        const fsig = self.fn_sigs.items[fsig_idx];

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
            });
        }

        var accesses: std.ArrayList(AccessRecord) = .empty;
        const prev_acc = self.current_accesses;
        const prev_ret = self.current_fn_ret;
        self.current_accesses = &accesses;
        self.current_fn_ret = fsig.ret;
        defer {
            self.current_accesses = prev_acc;
            self.current_fn_ret = prev_ret;
        }

        const body_res = try self.checkBlock(&f.body, fsig.ret, f.ret != null);
        if (f.ret != null and !fsig.ret.eql(.unit)) {
            if (f.body.tail != null or f.body.stmts.len == 0) {
                try self.checkAssignmentValue(f.body.span, fsig.ret, body_res);
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
            .param_types = fsig.params,
            .ret_type = fsig.ret,
            .reads = try reads_list.toOwnedSlice(self.alloc),
            .writes = try writes_list.toOwnedSlice(self.alloc),
            .preserves = &.{},
            .target_record = fsig.target_record,
            .has_extern_abi = false,
        });
    }

    fn containsAccess(slice: []const FieldAccessEffect, target: FieldAccessEffect) bool {
        for (slice) |item| {
            if (item.record_idx == target.record_idx and item.field_idx == target.field_idx) return true;
        }
        return false;
    }

    fn checkBlock(
        self: *Analyzer,
        blk: *const ast.Block,
        expected: ?*const Ty,
        enforce_tail: bool,
    ) std.mem.Allocator.Error!ExprResult {
        try self.pushScope();
        defer self.popScope();

        for (blk.stmts) |st| {
            try self.checkStmt(&st);
        }

        if (blk.tail) |tail| {
            const tail_expected = if (enforce_tail) expected else null;
            return try self.checkExpr(tail, tail_expected);
        }
        return .{ .ty = try self.allocTy(.unit), .range = null };
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
                const final_range = val_res.range orelse final_ty.rangeOf();
                try self.let_types.put(self.alloc, ls.span.start, final_ty);
                try self.bindPattern(ls.pattern, final_ty, final_range, ls.mutable);
            },
            .use_stmt => |us| {
                const rhs_res = try self.checkExpr(us.expr, null);
                for (us.patterns) |pat| {
                    try self.bindPattern(pat, rhs_res.ty, rhs_res.range, false);
                }
            },
            .assign_stmt => |asg| {
                const target_info = try self.checkWriteTarget(asg.target, asg.span);
                if (asg.op == .assign) {
                    const rhs_res = try self.checkExpr(asg.value, target_info.ty);
                    try self.checkAssignmentValue(asg.span, target_info.ty, rhs_res);
                } else {
                    const rhs_res = try self.checkExpr(asg.value, null);
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
                        }
                    }
                }
            },
            .while_stmt => |ws| {
                _ = try self.checkExpr(ws.cond, null);
                if (ws.decreases) |dec| _ = try self.checkExpr(dec, null);
                _ = try self.checkBlock(&ws.body, null, false);
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
                for (fs.body.stmts) |st| try self.checkStmt(&st);
                if (fs.body.tail) |tail| _ = try self.checkExpr(tail, null);
            },
            .expr_stmt => |es| {
                for (es.attrs) |attr| {
                    if (attr.payload == .layout) {
                        const col_lay = try self.resolveLayoutAttr(attr.span, attr.payload.layout);
                        if (col_lay) |cl| {
                            if (self.findCollectionTargetInExpr(es.expr)) |col_info| {
                                try self.checked_collections.append(self.alloc, .{
                                    .name = col_info.name,
                                    .layout = cl,
                                    .field_count = col_info.field_count,
                                });
                            }
                        }
                    }
                }
                _ = try self.checkExpr(es.expr, null);
            },
        }
    }

    fn findCollectionTargetInExpr(self: *Analyzer, expr: *const ast.Expr) ?struct { name: []const u8, field_count: usize } {
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
                return .{ .ty = vb.ty, .range = vb.range };
            },
            .field => |fld| {
                const base = try self.checkExpr(fld.target, null);
                const ridx = recordOfType(base.ty) orelse {
                    return .{ .ty = try self.allocTy(.err), .range = null };
                };
                const fname = fld.name.slice(self.source);
                const fidx = self.findRecordField(ridx, fname) orelse {
                    self.addError(.unknown_ident, fld.name, "unknown field on record");
                    return .{ .ty = try self.allocTy(.err), .range = null };
                };
                // Verify path-borrow authorization (`~>.{...}`).
                const root_name = self.extractRootIdent(fld.target);
                if (root_name) |rn| {
                    if (self.lookupVar(rn)) |vb| {
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
                    }
                    try self.recordAccess(rn, ridx, fidx, true, stmt_span);
                }
                const cf = self.record_defs.items[ridx].fields[fidx];
                return .{ .ty = cf.ty, .range = cf.ty.rangeOf() };
            },
            .index => |ix| {
                const base = try self.checkExpr(ix.target, null);
                _ = try self.checkExpr(ix.idx, null);
                const elem_ty: *const Ty = switch (base.ty.*) {
                    .slice => |sl| sl.elem,
                    .collection => |c| c.elem_ty,
                    else => try self.allocTy(.{ .int = .{ .signed = false, .bits = 8 } }),
                };
                if (self.extractRootIdent(ix.target)) |rn| {
                    if (self.lookupVar(rn)) |vb| {
                        if (vb.ty.* == .view and vb.ty.view.mode == .shared) {
                            self.addError(.borrow_conflict, ix.target.getSpan(), "cannot write through a shared view");
                        }
                    }
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

    fn recordAccess(
        self: *Analyzer,
        root_name: []const u8,
        record_idx: ?usize,
        field_idx: ?usize,
        is_write: bool,
        span: ast.Span,
    ) std.mem.Allocator.Error!void {
        // Check active view conflicts inside the same function scope:
        for (self.active_views.items) |av| {
            if (!std.mem.eql(u8, av.root_name, root_name)) continue;
            const same_field = (av.field_idx == null or field_idx == null or av.field_idx.? == field_idx.?);
            if (!same_field) {
                // Disjoint sibling concurrent exclusive view + access adds co-borrow conflict edge!
                if ((is_write or av.mode == .exclusive) and record_idx != null and av.field_idx != null and field_idx != null) {
                    try self.addConflictEdge(record_idx.?, av.field_idx.?, field_idx.?);
                }
                continue;
            }
            if (av.mode == .exclusive) {
                // OK only if reading/writing THROUGH the binding name itself (not checked on raw root inside same view unless mismatched binding).
            } else if (is_write) {
                self.addError(.borrow_conflict, span, "cannot mutate field while an active shared view locks it");
            }
        }
        if (self.current_accesses) |acc_list| {
            try acc_list.append(self.alloc, .{
                .root_name = root_name,
                .record_idx = record_idx,
                .field_idx = field_idx,
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
        if (!target.eql(val.ty.*)) {
            if (val.ty.* != .type_var and target.* != .type_var and target.* != .option and val.ty.* != .option) {
                self.addError(.type_mismatch, span, "expression type does not match expected type");
            }
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
                    return try self.checkPipeline(expr, b.left, b.right);
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
                return try self.checkCall(call_expr.span, call_expr.callee, call_expr.args, null);
            },
            .field => |fld| {
                const base = try self.checkExpr(fld.target, null);
                if (recordOfType(base.ty)) |ridx| {
                    const fname = fld.name.slice(self.source);
                    if (self.findRecordField(ridx, fname)) |fidx| {
                        if (self.extractRootIdent(fld.target)) |rn| {
                            try self.recordAccess(rn, ridx, fidx, false, fld.span);
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
                const base = try self.checkExpr(ix.target, null);
                _ = try self.checkExpr(ix.idx, null);
                const elem: *const Ty = switch (base.ty.*) {
                    .slice => |sl| sl.elem,
                    .collection => |c| c.elem_ty,
                    else => try self.allocTy(.{ .int = .{ .signed = false, .bits = 8 } }),
                };
                return .{ .ty = elem, .range = elem.rangeOf() };
            },
            .try_op => |t| {
                const inner = try self.checkExpr(t.operand, null);
                return switch (inner.ty.*) {
                    .option => |o| .{ .ty = o, .range = o.rangeOf() },
                    .result => |r| .{ .ty = r.ok, .range = r.ok.rangeOf() },
                    else => inner,
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
                    if (exp.* == .collection or exp.* == .slice) {
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
                var then_res: ExprResult = undefined;
                {
                    try self.pushScope();
                    defer self.popScope();
                    try self.applyBranchGuard(ie.cond, true);
                    for (ie.then_block.stmts) |st| try self.checkStmt(&st);
                    then_res = if (ie.then_block.tail) |t|
                        try self.checkExpr(t, expected)
                    else
                        .{ .ty = try self.allocTy(.unit), .range = null };
                }
                if (ie.else_branch) |eb| {
                    try self.pushScope();
                    defer self.popScope();
                    try self.applyBranchGuard(ie.cond, false);
                    const else_res = try self.checkExpr(eb, expected);
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
                var out: ExprResult = .{ .ty = expected orelse try self.allocTy(.unit), .range = null };
                var joined_int_range: ?IntRange = null;
                var all_int_arms = ce.arms.len > 0;
                for (ce.arms, 0..) |arm, ai| {
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
                try self.pushScope();
                defer self.popScope();
                const ps = try self.alloc.alloc(*const Ty, lam.params.len);
                for (lam.params, 0..) |p, pi| {
                    const pty = if (p.ty) |t| try self.resolveType(t) else try self.allocTy(.err);
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
                const ret_exp: ?*const Ty = if (lam.ret) |rt| try self.resolveType(rt) else null;
                const body_res = try self.checkBlock(&lam.body, ret_exp, ret_exp != null);
                const ret = ret_exp orelse body_res.ty;
                return .{ .ty = try self.allocTy(.{ .fn_ty = .{ .params = ps, .ret = ret } }), .range = null };
            },
            .view_expr => |vw| {
                const target_res = try self.checkExpr(vw.target, null);
                const mode = vw.mode orelse .shared;
                const root_name = self.extractRootIdent(vw.target) orelse "";
                var field_idx: ?usize = null;
                const ridx = recordOfType(target_res.ty) orelse blk: {
                    if (vw.target.* == .field) {
                        const bt = try self.checkExpr(vw.target.field.target, null);
                        if (recordOfType(bt.ty)) |ri| {
                            field_idx = self.findRecordField(ri, vw.target.field.name.slice(self.source));
                            break :blk ri;
                        }
                    }
                    break :blk null;
                };

                // Detect conflict with currently active views.
                for (self.active_views.items) |av| {
                    if (std.mem.eql(u8, av.root_name, root_name) and root_name.len > 0) {
                        const overlaps = (av.field_idx == null or field_idx == null or av.field_idx.? == field_idx.?);
                        if (overlaps and (mode == .exclusive or av.mode == .exclusive)) {
                            self.addError(.borrow_conflict, vw.span, "scoped view conflicts with active exclusive or shared reservation on the same path");
                        } else if (!overlaps and (mode == .exclusive or av.mode == .exclusive) and ridx != null and av.field_idx != null and field_idx != null) {
                            try self.addConflictEdge(ridx.?, av.field_idx.?, field_idx.?);
                        }
                    }
                }

                try self.pushScope();
                defer self.popScope();

                try self.active_views.append(self.alloc, .{
                    .root_name = root_name,
                    .record_idx = ridx,
                    .field_idx = field_idx,
                    .mode = mode,
                });

                if (vw.binding) |bspan| {
                    const view_ty = try self.allocTy(.{ .view = .{
                        .mode = mode,
                        .target = target_res.ty,
                        .target_record = ridx,
                    } });
                    try self.scopes.append(self.alloc, .{
                        .name = bspan.slice(self.source),
                        .ty = view_ty,
                        .range = null,
                        .mutable = mode == .exclusive,
                        .moved = false,
                        .authorized_paths = null,
                        .decl_span = bspan,
                    });
                }

                return try self.checkBlock(&vw.body, expected, false);
            },
            .fork_expr => |fk| {
                // Collect footprints independently for every concurrent branch.
                const branch_lists = try self.alloc.alloc(std.ArrayList(AccessRecord), fk.branches.len);
                const prev_acc = self.current_accesses;
                defer self.current_accesses = prev_acc;

                for (fk.branches, 0..) |*br, bi| {
                    branch_lists[bi] = .empty;
                    self.current_accesses = &branch_lists[bi];
                    _ = try self.checkBlock(br, null, false);
                }

                // Pairwise disjointness check (ScopedForkJoin.lean).
                var i: usize = 0;
                while (i < branch_lists.len) : (i += 1) {
                    var j: usize = i + 1;
                    while (j < branch_lists.len) : (j += 1) {
                        for (branch_lists[i].items) |a| {
                            for (branch_lists[j].items) |b| {
                                if (!std.mem.eql(u8, a.root_name, b.root_name)) continue;
                                if (!a.is_write and !b.is_write) continue; // Read-read safe!
                                const same_field = (a.field_idx == null or b.field_idx == null or a.field_idx.? == b.field_idx.?);
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

    fn checkPipeline(
        self: *Analyzer,
        full_expr: *const ast.Expr,
        left: *const ast.Expr,
        right: *const ast.Expr,
    ) std.mem.Allocator.Error!ExprResult {
        _ = full_expr;
        const left_res = try self.checkExpr(left, null);
        if (right.* == .call) {
            const call_res = try self.checkCall(right.call.span, right.call.callee, right.call.args, left_res);
            try self.expr_types.put(self.alloc, right, call_res.ty);
            return call_res;
        }
        return try self.checkExpr(right, null);
    }

    fn checkCall(
        self: *Analyzer,
        span: ast.Span,
        callee: *const ast.Expr,
        args: []const ast.CallArg,
        piped_recv: ?ExprResult,
    ) std.mem.Allocator.Error!ExprResult {
        // Built-in I/O (`println`, `print`, `eprintln`, `eprint` and `io.*` forms).
        if (self.builtinPrintKind(callee)) {
            for (args) |arg| {
                _ = try self.checkExpr(arg.value, null);
            }
            return .{ .ty = try self.allocTy(.unit), .range = null };
        }

        // Special-case collection/option/result higher-order combinators (`map_in_place`, `fold`).
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
                    _ = try self.checkBlock(&lam.body, null, false);
                    return .{ .ty = try self.allocTy(.unit), .range = null };
                }
            }
            if (self.findFnIndex(cname)) |fidx| {
                const fsig = self.fn_sigs.items[fidx];
                const recv_offset: usize = if (piped_recv != null) 1 else 0;
                if (piped_recv) |pr| {
                    if (fsig.params.len > 0) {
                        try self.checkAssignmentValue(span, fsig.params[0], pr);
                    }
                }
                for (args, 0..) |arg, ai| {
                    const param_idx = ai + recv_offset;
                    const expected_p = if (param_idx < fsig.params.len) fsig.params[param_idx] else null;
                    const ar = try self.checkExpr(arg.value, expected_p);
                    if (expected_p) |ep| {
                        if (!ep.isCopyable() and arg.value.* == .ident) {
                            const vname = arg.value.ident.slice(self.source);
                            if (self.lookupVar(vname)) |vb| {
                                if (!ep.eql(.{ .view = .{ .mode = .shared, .target = ep, .target_record = null } }) and ep.* != .slice and ep.* != .path_borrow) {
                                    vb.moved = true;
                                }
                            }
                        }
                        try self.checkAssignmentValue(arg.span, ep, ar);
                    }
                }
                return .{ .ty = fsig.ret, .range = fsig.ret.rangeOf() };
            }
        }

        if (callee.* == .upper_ident) {
            const cname = callee.upper_ident.slice(self.source);
            if (std.mem.eql(u8, cname, "Some") and args.len == 1) {
                const inner = try self.checkExpr(args[0].value, null);
                const inner_ty = try self.finalizeInferredType(args[0].span, inner);
                return .{ .ty = try self.allocTy(.{ .option = inner_ty }), .range = null };
            }
            if (std.mem.eql(u8, cname, "Ok") and args.len == 1) {
                const inner = try self.checkExpr(args[0].value, null);
                const inner_ty = try self.finalizeInferredType(args[0].span, inner);
                return .{ .ty = try self.allocTy(.{ .result = .{ .ok = inner_ty, .err = try self.allocTy(.err) } }), .range = null };
            }
            if (std.mem.eql(u8, cname, "Err") and args.len == 1) {
                const inner = try self.checkExpr(args[0].value, null);
                const inner_ty = try self.finalizeInferredType(args[0].span, inner);
                return .{ .ty = try self.allocTy(.{ .result = .{ .ok = try self.allocTy(.err), .err = inner_ty } }), .range = null };
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

        // Handle qualified constructors `Status.Moving(...)` or general function values.
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
                            const cur = vb.range orelse vb.ty.rangeOf() orelse return;
                            const effective_op = if (truthy) b.op else invertCmpOp(b.op) orelse return;
                            vb.range = narrowByCmp(cur, effective_op, bound) orelse cur;
                        }
                    }
                } else if (b.right.* == .ident) {
                    if (evalConstInt(self.source, b.left)) |bound| {
                        const vname = b.right.ident.slice(self.source);
                        if (self.lookupVar(vname)) |vb| {
                            const cur = vb.range orelse vb.ty.rangeOf() orelse return;
                            const flipped = flipCmpOp(b.op) orelse return;
                            const effective_op = if (truthy) flipped else invertCmpOp(flipped) orelse return;
                            vb.range = narrowByCmp(cur, effective_op, bound) orelse cur;
                        }
                    }
                }
            },
            else => {},
        }
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
            else => null,
        };
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
            const planned = try layout.planRecordLayout(self.alloc, schemas, rdef.conflicts.items);
            out[ridx] = .{
                .name = rdef.name,
                .span = rdef.span,
                .fields = rdef.fields,
                .conflicts = try rdef.conflicts.toOwnedSlice(self.alloc),
                .record_layout = planned,
                .collection_layout = rdef.collection_layout,
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

    fn checkLaws(self: *Analyzer, checked_records: []const CheckedRecord) std.mem.Allocator.Error!void {
        _ = checked_records;
        for (self.module.decls) |decl| {
            if (decl.kind != .law_decl) continue;
            const ld = decl.kind.law_decl;
            const lname = ld.name.slice(self.source);

            try self.pushScope();
            defer self.popScope();

            var law_rec_idx: ?usize = null;
            for (ld.params) |p| {
                const pty = if (p.ty) |t| try self.resolveType(t) else try self.allocTy(.err);
                if (law_rec_idx == null) law_rec_idx = recordOfType(pty);
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

            var verdict: LawVerdict = .unverified_symbolic;
            var all_proved = ld.clauses.len > 0;
            var violated = false;
            var has_symbolic_guard = false;

            for (ld.clauses) |cl| {
                switch (cl) {
                    .preserves => |pr| {
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
                        if (!violated and verdict == .unverified_symbolic) verdict = .proved_tier0;
                    },
                    .when => |wh| {
                        _ = try self.checkExpr(wh.expr, try self.allocTy(.bool));
                        try self.applyBranchGuard(wh.expr, true);
                        if (wh.expr.* == .binary) {
                            const wb = wh.expr.binary;
                            if (evalConstInt(self.source, wb.left) == null and evalConstInt(self.source, wb.right) == null) {
                                has_symbolic_guard = true;
                            }
                        }
                    },
                    .always => |al| {
                        _ = try self.checkExpr(al.expr, try self.allocTy(.bool));
                        switch (try self.evalIntervalPredicate(al.expr, has_symbolic_guard)) {
                            .always_true => {
                                if (verdict != .violated) verdict = .proved_interval;
                            },
                            .always_false, .can_fail => {
                                self.addError(.law_violation, al.span, "constitutional law 'always' violated over possible input intervals");
                                violated = true;
                            },
                            .unknown => {
                                all_proved = false;
                            },
                        }
                    },
                    .never => |nv| {
                        _ = try self.checkExpr(nv.expr, try self.allocTy(.bool));
                        switch (try self.evalIntervalPredicate(nv.expr, has_symbolic_guard)) {
                            .always_false => {
                                if (verdict != .violated) verdict = .proved_interval;
                            },
                            .always_true, .can_fail => {
                                self.addError(.law_violation, nv.span, "constitutional law 'never' can be satisfied on valid inputs");
                                violated = true;
                            },
                            .unknown => {
                                all_proved = false;
                            },
                        }
                    },
                    .expr => |ex| {
                        _ = try self.checkExpr(ex.expr, try self.allocTy(.bool));
                        switch (try self.evalIntervalPredicate(ex.expr, has_symbolic_guard)) {
                            .always_true => {
                                if (verdict != .violated) verdict = .proved_interval;
                            },
                            .can_fail, .always_false => {
                                self.addError(.law_violation, ex.span, "constitutional law predicate falsified on interval bounds");
                                violated = true;
                            },
                            .unknown => {
                                all_proved = false;
                            },
                        }
                    },
                }
            }

            if (violated) {
                verdict = .violated;
            } else if (!all_proved and verdict == .proved_interval) {
                verdict = .unverified_symbolic;
            }

            try self.checked_laws.append(self.alloc, .{
                .name = lname,
                .span = decl.span,
                .verdict = verdict,
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
        .current_accesses = null,
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
    };
}
