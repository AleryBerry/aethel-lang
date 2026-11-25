const std = @import("std");
const Io = std.Io;
const ast = @import("ast.zig");
const int_range = @import("int_range.zig");
const sema = @import("sema.zig");

/// Emit a self-contained Zig 0.17.0 source file implementing a typechecked Aethel module.
/// Intended for compilation via Zig's built-in compiler (`zig build-exe -fno-llvm -fno-lld`).
pub fn emitZig(
    tree: *const ast.Ast,
    checked: *const sema.CheckedModule,
    writer: *Io.Writer,
) Io.Writer.Error!void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    var em = Emitter{
        .alloc = arena.allocator(),
        .tree = tree,
        .checked = checked,
        .w = writer,
    };
    try em.emitModule();
}

const ScopeVar = struct {
    name: []const u8,
    ty: ?*const sema.Ty,
    is_mut: bool,
    is_owned_dyn: bool = false,
    has_moved_flag: bool = false,
};

const Emitter = struct {
    alloc: std.mem.Allocator,
    tree: *const ast.Ast,
    checked: *const sema.CheckedModule,
    w: *Io.Writer,
    label_counter: usize = 0,
    indent: usize = 0,
    current_fn_ret: ?*const sema.Ty = null,
    scope_vars: std.ArrayList(ScopeVar) = .empty,
    deref_idents: std.ArrayList([]const u8) = .empty,
    ctx_value_idents: std.ArrayList([]const u8) = .empty,

    fn pushScopeVars(self: *const Emitter) usize {
        return self.scope_vars.items.len;
    }

    fn popScopeVars(self: *Emitter, mark: usize) void {
        self.scope_vars.shrinkRetainingCapacity(mark);
    }

    fn bindScopeVar(self: *Emitter, name: []const u8, ty: ?*const sema.Ty, is_mut: bool) void {
        self.scope_vars.append(self.alloc, .{
            .name = name,
            .ty = ty,
            .is_mut = is_mut,
            .is_owned_dyn = false,
            .has_moved_flag = false,
        }) catch {};
    }

    fn bindOwnedScopeVar(self: *Emitter, name: []const u8, ty: ?*const sema.Ty, is_mut: bool, has_moved_flag: bool) void {
        self.scope_vars.append(self.alloc, .{
            .name = name,
            .ty = ty,
            .is_mut = is_mut,
            .is_owned_dyn = true,
            .has_moved_flag = has_moved_flag,
        }) catch {};
    }

    fn isOwnedDynamicTy(ty: ?*const sema.Ty) bool {
        const t = ty orelse return false;
        return switch (t.*) {
            .vec, .map, .set, .deque => true,
            else => false,
        };
    }

    fn lookupScopeVar(self: *const Emitter, name: []const u8) ?ScopeVar {
        var i = self.scope_vars.items.len;
        while (i > 0) {
            i -= 1;
            if (std.mem.eql(u8, self.scope_vars.items[i].name, name)) {
                return self.scope_vars.items[i];
            }
        }
        return null;
    }

    fn isDerefIdent(self: *const Emitter, name: []const u8) bool {
        for (self.deref_idents.items) |dn| {
            if (std.mem.eql(u8, dn, name)) return true;
        }
        return false;
    }

    fn isCtxValueIdent(self: *const Emitter, name: []const u8) bool {
        for (self.ctx_value_idents.items) |cn| {
            if (std.mem.eql(u8, cn, name)) return true;
        }
        return false;
    }

    fn nextLabel(self: *Emitter) usize {
        self.label_counter += 1;
        return self.label_counter;
    }

    fn writeIndent(self: *Emitter) Io.Writer.Error!void {
        var i: usize = 0;
        while (i < self.indent) : (i += 1) {
            try self.w.writeAll("    ");
        }
    }

    fn sourceOf(self: *const Emitter, span: ast.Span) []const u8 {
        return span.slice(self.tree.source);
    }

    fn emitModule(self: *Emitter) Io.Writer.Error!void {
        try self.emitPreamble();

        // Top-level imports are module compile-time comments in single-file lowering.
        for (self.tree.module.decls) |decl| {
            switch (decl.kind) {
                .import_decl => |imp| {
                    try self.w.writeAll("// import ");
                    for (imp.path, 0..) |seg, i| {
                        if (i > 0) try self.w.writeByte('/');
                        try self.w.writeAll(self.sourceOf(seg));
                    }
                    try self.w.writeByte('\n');
                },
                else => {},
            }
        }

        // 1. Type declarations (records, ADTs, aliases, opaques)
        for (self.tree.module.decls) |decl| {
            if (decl.kind == .type_decl) {
                try self.emitTypeDecl(&decl);
                try self.w.writeByte('\n');
            }
        }

        // 2. Constants
        for (self.tree.module.decls) |decl| {
            if (decl.kind == .const_decl) {
                try self.emitConstDecl(&decl);
            }
        }

        // 3. Extern C-ABI & @external(rust) declarations (Rust staticlib bridge)
        for (self.tree.module.decls) |decl| {
            switch (decl.kind) {
                .extern_decl => try self.emitExternDecl(&decl),
                .fn_decl => |fd| if (!fd.has_body) {
                    try self.emitExternalFnProto(&decl);
                },
                else => {},
            }
        }

        // 4. Trait instances (compile-time zero-overhead witness structs/functors)
        for (self.checked.instances) |*inst| {
            try self.emitInstanceDecl(inst);
            try self.w.writeByte('\n');
        }

        // 5. Functions & erased Constitutional Laws
        for (self.tree.module.decls) |decl| {
            switch (decl.kind) {
                .fn_decl => |fd| {
                    if (fd.has_body) {
                        try self.emitFnDecl(&decl);
                        try self.w.writeByte('\n');
                    }
                },
                .law_decl => |ld| {
                    const lname = self.sourceOf(ld.name);
                    var verdict_str: []const u8 = "checked";
                    for (self.checked.laws) |cl| {
                        if (std.mem.eql(u8, cl.name, lname)) {
                            verdict_str = @tagName(cl.verdict);
                            break;
                        }
                    }
                    try self.w.print("// law {s}: erased ({s})\n", .{ lname, verdict_str });
                },
                .trait_decl => |tr| {
                    try self.w.print("// trait {s}: erased (laws checked per instance)\n", .{self.sourceOf(tr.name)});
                },
                else => {},
            }
        }
    }

    fn emitPreamble(self: *Emitter) Io.Writer.Error!void {
        try self.w.writeAll(
            \\// Generated by Aethel compiler (Zig built-in compiler backend — no LLVM)
            \\const std = @import("std");
            \\
            \\var aethel_io: std.Io = undefined;
            \\var aethel_raw_arena: std.mem.Allocator = std.heap.smp_allocator;
            \\var aethel_arena_lock: std.atomic.Value(bool) = .init(false);
            \\var aethel_print_lock: std.atomic.Value(bool) = .init(false);
            \\var aethel_gpa: std.mem.Allocator = std.heap.smp_allocator;
            \\var aethel_str_buf: ?[*]u8 = null;
            \\var aethel_str_len: usize = 0;
            \\var aethel_str_cap: usize = 0;
            \\
            \\fn aethelLockAcquire(lock: *std.atomic.Value(bool)) void {
            \\    while (lock.cmpxchgWeak(false, true, .acquire, .monotonic) != null) {
            \\        std.atomic.spinLoopHint();
            \\    }
            \\}
            \\
            \\fn aethelLockRelease(lock: *std.atomic.Value(bool)) void {
            \\    lock.store(false, .release);
            \\}
            \\
            \\fn aethelSyncAlloc(_: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
            \\    aethelLockAcquire(&aethel_arena_lock);
            \\    defer aethelLockRelease(&aethel_arena_lock);
            \\    return aethel_raw_arena.vtable.alloc(aethel_raw_arena.ptr, len, alignment, ret_addr);
            \\}
            \\
            \\fn aethelSyncResize(_: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
            \\    aethelLockAcquire(&aethel_arena_lock);
            \\    defer aethelLockRelease(&aethel_arena_lock);
            \\    return aethel_raw_arena.vtable.resize(aethel_raw_arena.ptr, memory, alignment, new_len, ret_addr);
            \\}
            \\
            \\fn aethelSyncRemap(_: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
            \\    aethelLockAcquire(&aethel_arena_lock);
            \\    defer aethelLockRelease(&aethel_arena_lock);
            \\    return aethel_raw_arena.vtable.remap(aethel_raw_arena.ptr, memory, alignment, new_len, ret_addr);
            \\}
            \\
            \\fn aethelSyncFree(_: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
            \\    aethelLockAcquire(&aethel_arena_lock);
            \\    defer aethelLockRelease(&aethel_arena_lock);
            \\    aethel_raw_arena.vtable.free(aethel_raw_arena.ptr, memory, alignment, ret_addr);
            \\}
            \\
            \\const aethel_alloc: std.mem.Allocator = .{
            \\    .ptr = undefined,
            \\    .vtable = &.{
            \\        .alloc = aethelSyncAlloc,
            \\        .resize = aethelSyncResize,
            \\        .remap = aethelSyncRemap,
            \\        .free = aethelSyncFree,
            \\    },
            \\};
            \\
            \\fn aethelPrint(args: anytype, newline: bool, to_stderr: bool) void {
            \\    aethelLockAcquire(&aethel_print_lock);
            \\    defer aethelLockRelease(&aethel_print_lock);
            \\    var buf: [4096]u8 = undefined;
            \\    const file: std.Io.File = if (to_stderr) .stderr() else .stdout();
            \\    var fw: std.Io.File.Writer = .init(file, aethel_io, &buf);
            \\    const w = &fw.interface;
            \\    inline for (args) |arg| {
            \\        aethelWriteVal(w, arg);
            \\    }
            \\    if (newline) {
            \\        w.writeByte('\n') catch {};
            \\    }
            \\    w.flush() catch {};
            \\}
            \\
            \\fn aethelWriteVal(w: *std.Io.Writer, val: anytype) void {
            \\    const T = @TypeOf(val);
            \\    if (T == []const u8 or T == []u8) {
            \\        w.writeAll(val) catch {};
            \\        return;
            \\    }
            \\    switch (@typeInfo(T)) {
            \\        .pointer => |ptr| {
            \\            if (ptr.size == .one) {
            \\                switch (@typeInfo(ptr.child)) {
            \\                    .array => |arr| if (arr.child == u8) {
            \\                        w.writeAll(val) catch {};
            \\                        return;
            \\                    },
            \\                    else => {},
            \\                }
            \\            }
            \\            w.print("{any}", .{val}) catch {};
            \\        },
            \\        .int => |info| {
            \\            if (info.bits <= 128) {
            \\                const Wide = if (info.signedness == .signed) i128 else u128;
            \\                w.print("{d}", .{@as(Wide, val)}) catch {};
            \\            } else {
            \\                w.print("{d}", .{val}) catch {};
            \\            }
            \\        },
            \\        .comptime_int, .float, .comptime_float => w.print("{d}", .{val}) catch {},
            \\        .bool => w.writeAll(if (val) "true" else "false") catch {},
            \\        .@"enum" => w.writeAll(@tagName(val)) catch {},
            \\        else => w.print("{any}", .{val}) catch {},
            \\    }
            \\}
            \\
            \\fn aethelConcat(a: []const u8, b: []const u8) []const u8 {
            \\    if (a.len == 0) return b;
            \\    if (b.len == 0) return a;
            \\    aethelLockAcquire(&aethel_arena_lock);
            \\    defer aethelLockRelease(&aethel_arena_lock);
            \\    if (aethel_str_buf) |buf| {
            \\        const base = @intFromPtr(buf);
            \\        const ap = @intFromPtr(a.ptr);
            \\        if (ap >= base and ap + a.len == base + aethel_str_len and aethel_str_len + b.len <= aethel_str_cap) {
            \\            @memcpy(buf[aethel_str_len .. aethel_str_len + b.len], b);
            \\            const off = ap - base;
            \\            aethel_str_len += b.len;
            \\            return buf[off .. off + a.len + b.len];
            \\        }
            \\    }
            \\    const need = a.len + b.len;
            \\    const new_cap: usize = @max(@as(usize, 4096), need * 2);
            \\    const chunk = aethel_raw_arena.alloc(u8, new_cap) catch @panic("aethel: out of memory");
            \\    @memcpy(chunk[0..a.len], a);
            \\    @memcpy(chunk[a.len..need], b);
            \\    aethel_str_buf = chunk.ptr;
            \\    aethel_str_len = need;
            \\    aethel_str_cap = new_cap;
            \\    return chunk[0..need];
            \\}
            \\
            \\fn aethelStrRepeat(s: []const u8, count: u64) []const u8 {
            \\    if (s.len == 0 or count == 0) return "";
            \\    if (count == 1) return s;
            \\    const c: usize = @intCast(count);
            \\    const total = s.len * c;
            \\    const out = aethel_alloc.alloc(u8, total) catch @panic("aethel: out of memory");
            \\    @memcpy(out[0..s.len], s);
            \\    var filled: usize = s.len;
            \\    while (filled < total) {
            \\        const step = @min(filled, total - filled);
            \\        @memcpy(out[filled .. filled + step], out[0..step]);
            \\        filled += step;
            \\    }
            \\    return out;
            \\}
            \\
            \\fn aethelClamp(comptime T: type, val: i128, comptime lo: i128, comptime hi: i128) T {
            \\    const clamped = @min(@max(val, lo), hi);
            \\    return @intCast(clamped);
            \\}
            \\
            \\fn AethelResult(comptime T: type, comptime E: type) type {
            \\    return union(enum) { Ok: T, Err: E };
            \\}
            \\
            \\fn AethelCallRet(comptime F: type) type {
            \\    const info = @typeInfo(F);
            \\    if (info == .@"struct" and @hasDecl(F, "call")) {
            \\        return @typeInfo(@TypeOf(F.call)).@"fn".return_type.?;
            \\    } else if (info == .pointer) {
            \\        const cinfo = @typeInfo(info.pointer.child);
            \\        if (cinfo == .@"fn") return cinfo.@"fn".return_type.?;
            \\    } else if (info == .@"fn") {
            \\        return info.@"fn".return_type.?;
            \\    }
            \\    return void;
            \\}
            \\
            \\fn aethelCall(f: anytype, args: anytype) AethelCallRet(@TypeOf(f)) {
            \\    const F = @TypeOf(f);
            \\    if (@typeInfo(F) == .@"struct" and @hasDecl(F, "call")) {
            \\        return @call(.auto, F.call, .{f} ++ args);
            \\    } else {
            \\        return @call(.auto, f, args);
            \\    }
            \\}
            \\
            \\fn aethelHashVal(val: anytype) u64 {
            \\    const T = @TypeOf(val);
            \\    if (T == []const u8 or T == []u8) {
            \\        return std.hash.Wyhash.hash(0, val);
            \\    }
            \\    switch (@typeInfo(T)) {
            \\        .int => |info| {
            \\            if (info.bits <= 64) {
            \\                const uval: u64 = if (info.signedness == .signed) @bitCast(@as(i64, @intCast(val))) else @intCast(val);
            \\                return std.hash.Wyhash.hash(0, std.mem.asBytes(&uval));
            \\            }
            \\            return std.hash.Wyhash.hash(0, std.mem.asBytes(&val));
            \\        },
            \\        .bool => return if (val) 0x9e3779b97f4a7c15 else 0x517cc1b727220a95,
            \\        .@"enum" => {
            \\            const tag: usize = @intFromEnum(val);
            \\            return std.hash.Wyhash.hash(0, std.mem.asBytes(&tag));
            \\        },
            \\        .optional => {
            \\            if (val) |inner| return aethelHashVal(inner) ^ 0x5555555555555555;
            \\            return 0xaaaaaaaaaaaaaaaa;
            \\        },
            \\        .@"struct" => |si| {
            \\            var h: u64 = 0x243f6a8885a308d3;
            \\            inline for (si.fields) |fld| {
            \\                h = h *% 0x9e3779b185ebca87 +% aethelHashVal(@field(val, fld.name));
            \\            }
            \\            return h;
            \\        },
            \\        .pointer => |ptr| {
            \\            if (ptr.size == .one and @typeInfo(ptr.child) == .array and @typeInfo(ptr.child).array.child == u8) {
            \\                return std.hash.Wyhash.hash(0, val);
            \\            }
            \\            return std.hash.Wyhash.hash(0, std.mem.asBytes(&val));
            \\        },
            \\        else => return std.hash.Wyhash.hash(0, std.mem.asBytes(&val)),
            \\    }
            \\}
            \\
            \\fn aethelEqlVal(a: anytype, b: @TypeOf(a)) bool {
            \\    const T = @TypeOf(a);
            \\    if (T == []const u8 or T == []u8) {
            \\        return std.mem.eql(u8, a, b);
            \\    }
            \\    switch (@typeInfo(T)) {
            \\        .optional => {
            \\            if (a) |va| {
            \\                if (b) |vb| return aethelEqlVal(va, vb);
            \\                return false;
            \\            }
            \\            return b == null;
            \\        },
            \\        .@"struct" => |si| {
            \\            inline for (si.fields) |fld| {
            \\                if (!aethelEqlVal(@field(a, fld.name), @field(b, fld.name))) return false;
            \\            }
            \\            return true;
            \\        },
            \\        else => return std.meta.eql(a, b),
            \\    }
            \\}
            \\
            \\fn aethelStrStartsWith(s: []const u8, pre: []const u8) bool {
            \\    return std.mem.startsWith(u8, s, pre);
            \\}
            \\
            \\fn aethelStrEndsWith(s: []const u8, suf: []const u8) bool {
            \\    return std.mem.endsWith(u8, s, suf);
            \\}
            \\
            \\fn aethelStrContains(s: []const u8, sub: []const u8) bool {
            \\    return std.mem.indexOf(u8, s, sub) != null;
            \\}
            \\
            \\fn aethelStrByteAt(s: []const u8, idx: u64) ?u8 {
            \\    const i: usize = @intCast(idx);
            \\    if (i >= s.len) return null;
            \\    return s[i];
            \\}
            \\
            \\fn aethelStrSlice(s: []const u8, lo: u64, hi: u64) []const u8 {
            \\    const a: usize = @min(@as(usize, @intCast(lo)), s.len);
            \\    const b: usize = @max(a, @min(@as(usize, @intCast(hi)), s.len));
            \\    return s[a..b];
            \\}
            \\
            \\fn AethelVec(comptime T: type) type {
            \\    return struct {
            \\        items_ptr: ?[*]align(64) T = null,
            \\        len: usize = 0,
            \\        cap: usize = 0,
            \\
            \\        pub fn new() @This() {
            \\            return .{};
            \\        }
            \\
            \\        pub fn withCapacity(req_cap: u64) @This() {
            \\            var self = @This(){};
            \\            if (req_cap > 0) self.ensureExactCap(@intCast(req_cap));
            \\            return self;
            \\        }
            \\
            \\        pub fn fromSlice(src: []const T) @This() {
            \\            var self = @This(){};
            \\            if (src.len > 0) {
            \\                self.ensureExactCap(src.len);
            \\                if (self.items_ptr) |p| {
            \\                    @memcpy(p[0..src.len], src);
            \\                }
            \\                self.len = src.len;
            \\            }
            \\            return self;
            \\        }
            \\
            \\        fn allocExactCap(self: *@This(), new_cap: usize) void {
            \\            if (@sizeOf(T) == 0) {
            \\                self.cap = new_cap;
            \\                return;
            \\            }
            \\            const new_mem = aethel_gpa.alignedAlloc(T, .@"64", new_cap) catch @panic("aethel: out of memory");
            \\            if (self.items_ptr) |old_p| {
            \\                if (self.len > 0) @memcpy(new_mem[0..self.len], old_p[0..self.len]);
            \\                if (self.cap > 0) aethel_gpa.free(old_p[0..self.cap]);
            \\            }
            \\            self.items_ptr = new_mem.ptr;
            \\            self.cap = new_cap;
            \\        }
            \\
            \\        fn ensureExactCap(self: *@This(), exact_cap: usize) void {
            \\            if (exact_cap <= self.cap) return;
            \\            self.allocExactCap(exact_cap);
            \\        }
            \\
            \\        fn ensureCap(self: *@This(), min_cap: usize) void {
            \\            if (min_cap <= self.cap) return;
            \\            var new_cap: usize = if (self.cap == 0) 8 else self.cap * 2;
            \\            while (new_cap < min_cap) new_cap *= 2;
            \\            self.allocExactCap(new_cap);
            \\        }
            \\
            \\        pub fn reserve(self: *@This(), additional: u64) void {
            \\            self.ensureCap(self.len + @as(usize, @intCast(additional)));
            \\        }
            \\
            \\        pub fn push(self: *@This(), val: T) void {
            \\            if (self.len == self.cap) self.ensureCap(self.len + 1);
            \\            if (self.items_ptr) |p| p[self.len] = val;
            \\            self.len += 1;
            \\        }
            \\
            \\        pub fn pop(self: *@This()) ?T {
            \\            if (self.len == 0) return null;
            \\            self.len -= 1;
            \\            return if (self.items_ptr) |p| p[self.len] else null;
            \\        }
            \\
            \\        pub fn get(self: @This(), idx: u64) ?T {
            \\            const i: usize = @intCast(idx);
            \\            if (i >= self.len) return null;
            \\            return if (self.items_ptr) |p| p[i] else null;
            \\        }
            \\
            \\        pub fn set(self: *@This(), idx: u64, val: T) bool {
            \\            const i: usize = @intCast(idx);
            \\            if (i >= self.len) return false;
            \\            if (self.items_ptr) |p| p[i] = val;
            \\            return true;
            \\        }
            \\
            \\        pub fn swapRemove(self: *@This(), idx: u64) ?T {
            \\            const i: usize = @intCast(idx);
            \\            if (i >= self.len) return null;
            \\            const p = self.items_ptr orelse return null;
            \\            const removed = p[i];
            \\            self.len -= 1;
            \\            if (i != self.len) p[i] = p[self.len];
            \\            return removed;
            \\        }
            \\
            \\        pub fn clear(self: *@This()) void {
            \\            self.len = 0;
            \\        }
            \\
            \\        pub fn asSlice(self: @This()) []const T {
            \\            if (self.len == 0) return &[_]T{};
            \\            return if (self.items_ptr) |p| p[0..self.len] else &[_]T{};
            \\        }
            \\
            \\        pub fn mutSlice(self: *@This()) []T {
            \\            const empty = @as([*]T, @ptrFromInt(@alignOf(T)))[0..0];
            \\            if (self.len == 0) return empty;
            \\            return if (self.items_ptr) |p| p[0..self.len] else empty;
            \\        }
            \\
            \\        pub fn slice(self: @This(), lo: usize, hi: usize) []T {
            \\            const empty = @as([*]T, @ptrFromInt(@alignOf(T)))[0..0];
            \\            const p = self.items_ptr orelse return empty;
            \\            return p[lo..hi];
            \\        }
            \\
            \\        pub fn deinit(self: @This()) void {
            \\            if (@sizeOf(T) > 0 and self.cap > 0) {
            \\                if (self.items_ptr) |p| aethel_gpa.free(p[0..self.cap]);
            \\            }
            \\        }
            \\    };
            \\}
            \\
            \\fn AethelMap(comptime K: type, comptime V: type) type {
            \\    return struct {
            \\        ctrl: ?[*]align(64) u8 = null,
            \\        keys: ?[*]K = null,
            \\        vals: ?[*]V = null,
            \\        len: usize = 0,
            \\        used: usize = 0,
            \\        cap: usize = 0,
            \\
            \\        pub fn new() @This() {
            \\            return .{};
            \\        }
            \\
            \\        pub fn withCapacity(req_cap: u64) @This() {
            \\            var self = @This(){};
            \\            if (req_cap > 0) {
            \\                var c: usize = 8;
            \\                while (c * 7 < @as(usize, @intCast(req_cap)) * 8) c *= 2;
            \\                self.rehash(c);
            \\            }
            \\            return self;
            \\        }
            \\
            \\        fn rehash(self: *@This(), new_cap: usize) void {
            \\            const new_ctrl = aethel_gpa.alignedAlloc(u8, .@"64", new_cap) catch @panic("aethel: out of memory");
            \\            @memset(new_ctrl, 0);
            \\            const new_keys = aethel_gpa.alloc(K, new_cap) catch @panic("aethel: out of memory");
            \\            const new_vals = aethel_gpa.alloc(V, new_cap) catch @panic("aethel: out of memory");
            \\            const mask = new_cap - 1;
            \\            var new_len: usize = 0;
            \\            if (self.cap > 0 and self.ctrl != null and self.keys != null and self.vals != null) {
            \\                const oc = self.ctrl.?;
            \\                const ok = self.keys.?;
            \\                const ov = self.vals.?;
            \\                for (0..self.cap) |i| {
            \\                    if ((oc[i] & 0x80) != 0) {
            \\                        const k = ok[i];
            \\                        const h = aethelHashVal(k);
            \\                        const h2: u8 = @as(u8, @truncate((h >> 57) & 0x7F)) | 0x80;
            \\                        var idx: usize = @intCast(h & mask);
            \\                        while (new_ctrl[idx] != 0) idx = (idx + 1) & mask;
            \\                        new_ctrl[idx] = h2;
            \\                        new_keys[idx] = k;
            \\                        new_vals[idx] = ov[i];
            \\                        new_len += 1;
            \\                    }
            \\                }
            \\                aethel_gpa.free(oc[0..self.cap]);
            \\                aethel_gpa.free(ok[0..self.cap]);
            \\                aethel_gpa.free(ov[0..self.cap]);
            \\            }
            \\            self.ctrl = new_ctrl.ptr;
            \\            self.keys = new_keys.ptr;
            \\            self.vals = new_vals.ptr;
            \\            self.cap = new_cap;
            \\            self.len = new_len;
            \\            self.used = new_len;
            \\        }
            \\
            \\        pub fn insert(self: *@This(), k: K, v: V) ?V {
            \\            if (self.cap == 0) {
            \\                self.rehash(8);
            \\            } else if ((self.used + 1) * 8 > self.cap * 7) {
            \\                const next_cap = if (self.len * 2 <= self.cap) self.cap else self.cap * 2;
            \\                self.rehash(next_cap);
            \\            }
            \\            const c = self.ctrl.?;
            \\            const ks = self.keys.?;
            \\            const vs = self.vals.?;
            \\            const mask = self.cap - 1;
            \\            const h = aethelHashVal(k);
            \\            const h2: u8 = @as(u8, @truncate((h >> 57) & 0x7F)) | 0x80;
            \\            var idx: usize = @intCast(h & mask);
            \\            var first_tomb: ?usize = null;
            \\            while (true) {
            \\                const slot = c[idx];
            \\                if (slot == 0) {
            \\                    const dst = first_tomb orelse idx;
            \\                    if (first_tomb == null) self.used += 1;
            \\                    c[dst] = h2;
            \\                    ks[dst] = k;
            \\                    vs[dst] = v;
            \\                    self.len += 1;
            \\                    return null;
            \\                }
            \\                if (slot == 1) {
            \\                    if (first_tomb == null) first_tomb = idx;
            \\                } else if (slot == h2 and aethelEqlVal(ks[idx], k)) {
            \\                    const prev = vs[idx];
            \\                    vs[idx] = v;
            \\                    return prev;
            \\                }
            \\                idx = (idx + 1) & mask;
            \\            }
            \\        }
            \\
            \\        pub fn put(self: *@This(), k: K, v: V) void {
            \\            _ = self.insert(k, v);
            \\        }
            \\
            \\        pub fn get(self: @This(), k: K) ?V {
            \\            if (self.cap == 0 or self.len == 0) return null;
            \\            const c = self.ctrl orelse return null;
            \\            const ks = self.keys orelse return null;
            \\            const vs = self.vals orelse return null;
            \\            const mask = self.cap - 1;
            \\            const h = aethelHashVal(k);
            \\            const h2: u8 = @as(u8, @truncate((h >> 57) & 0x7F)) | 0x80;
            \\            var idx: usize = @intCast(h & mask);
            \\            while (true) {
            \\                const slot = c[idx];
            \\                if (slot == 0) return null;
            \\                if (slot == h2 and aethelEqlVal(ks[idx], k)) return vs[idx];
            \\                idx = (idx + 1) & mask;
            \\            }
            \\        }
            \\
            \\        pub fn contains(self: @This(), k: K) bool {
            \\            return self.get(k) != null;
            \\        }
            \\
            \\        pub fn remove(self: *@This(), k: K) ?V {
            \\            if (self.cap == 0 or self.len == 0) return null;
            \\            const c = self.ctrl orelse return null;
            \\            const ks = self.keys orelse return null;
            \\            const vs = self.vals orelse return null;
            \\            const mask = self.cap - 1;
            \\            const h = aethelHashVal(k);
            \\            const h2: u8 = @as(u8, @truncate((h >> 57) & 0x7F)) | 0x80;
            \\            var idx: usize = @intCast(h & mask);
            \\            while (true) {
            \\                const slot = c[idx];
            \\                if (slot == 0) return null;
            \\                if (slot == h2 and aethelEqlVal(ks[idx], k)) {
            \\                    c[idx] = 1;
            \\                    self.len -= 1;
            \\                    return vs[idx];
            \\                }
            \\                idx = (idx + 1) & mask;
            \\            }
            \\        }
            \\
            \\        pub fn clear(self: *@This()) void {
            \\            if (self.cap > 0) {
            \\                if (self.ctrl) |c| @memset(c[0..self.cap], 0);
            \\            }
            \\            self.len = 0;
            \\            self.used = 0;
            \\        }
            \\
            \\        pub fn deinit(self: @This()) void {
            \\            if (self.cap > 0) {
            \\                if (self.ctrl) |c| aethel_gpa.free(c[0..self.cap]);
            \\                if (self.keys) |ks| aethel_gpa.free(ks[0..self.cap]);
            \\                if (self.vals) |vs| aethel_gpa.free(vs[0..self.cap]);
            \\            }
            \\        }
            \\    };
            \\}
            \\
            \\fn AethelSet(comptime K: type) type {
            \\    return struct {
            \\        ctrl: ?[*]align(64) u8 = null,
            \\        keys: ?[*]K = null,
            \\        len: usize = 0,
            \\        used: usize = 0,
            \\        cap: usize = 0,
            \\
            \\        pub fn new() @This() {
            \\            return .{};
            \\        }
            \\
            \\        pub fn withCapacity(req_cap: u64) @This() {
            \\            var self = @This(){};
            \\            if (req_cap > 0) {
            \\                var c: usize = 8;
            \\                while (c * 7 < @as(usize, @intCast(req_cap)) * 8) c *= 2;
            \\                self.rehash(c);
            \\            }
            \\            return self;
            \\        }
            \\
            \\        fn rehash(self: *@This(), new_cap: usize) void {
            \\            const new_ctrl = aethel_gpa.alignedAlloc(u8, .@"64", new_cap) catch @panic("aethel: out of memory");
            \\            @memset(new_ctrl, 0);
            \\            const new_keys = aethel_gpa.alloc(K, new_cap) catch @panic("aethel: out of memory");
            \\            const mask = new_cap - 1;
            \\            var new_len: usize = 0;
            \\            if (self.cap > 0 and self.ctrl != null and self.keys != null) {
            \\                const oc = self.ctrl.?;
            \\                const ok = self.keys.?;
            \\                for (0..self.cap) |i| {
            \\                    if ((oc[i] & 0x80) != 0) {
            \\                        const k = ok[i];
            \\                        const h = aethelHashVal(k);
            \\                        const h2: u8 = @as(u8, @truncate((h >> 57) & 0x7F)) | 0x80;
            \\                        var idx: usize = @intCast(h & mask);
            \\                        while (new_ctrl[idx] != 0) idx = (idx + 1) & mask;
            \\                        new_ctrl[idx] = h2;
            \\                        new_keys[idx] = k;
            \\                        new_len += 1;
            \\                    }
            \\                }
            \\                aethel_gpa.free(oc[0..self.cap]);
            \\                aethel_gpa.free(ok[0..self.cap]);
            \\            }
            \\            self.ctrl = new_ctrl.ptr;
            \\            self.keys = new_keys.ptr;
            \\            self.cap = new_cap;
            \\            self.len = new_len;
            \\            self.used = new_len;
            \\        }
            \\
            \\        pub fn insert(self: *@This(), k: K) bool {
            \\            if (self.cap == 0) {
            \\                self.rehash(8);
            \\            } else if ((self.used + 1) * 8 > self.cap * 7) {
            \\                const next_cap = if (self.len * 2 <= self.cap) self.cap else self.cap * 2;
            \\                self.rehash(next_cap);
            \\            }
            \\            const c = self.ctrl.?;
            \\            const ks = self.keys.?;
            \\            const mask = self.cap - 1;
            \\            const h = aethelHashVal(k);
            \\            const h2: u8 = @as(u8, @truncate((h >> 57) & 0x7F)) | 0x80;
            \\            var idx: usize = @intCast(h & mask);
            \\            var first_tomb: ?usize = null;
            \\            while (true) {
            \\                const slot = c[idx];
            \\                if (slot == 0) {
            \\                    const dst = first_tomb orelse idx;
            \\                    if (first_tomb == null) self.used += 1;
            \\                    c[dst] = h2;
            \\                    ks[dst] = k;
            \\                    self.len += 1;
            \\                    return true;
            \\                }
            \\                if (slot == 1) {
            \\                    if (first_tomb == null) first_tomb = idx;
            \\                } else if (slot == h2 and aethelEqlVal(ks[idx], k)) {
            \\                    return false;
            \\                }
            \\                idx = (idx + 1) & mask;
            \\            }
            \\        }
            \\
            \\        pub fn contains(self: @This(), k: K) bool {
            \\            if (self.cap == 0 or self.len == 0) return false;
            \\            const c = self.ctrl orelse return false;
            \\            const ks = self.keys orelse return false;
            \\            const mask = self.cap - 1;
            \\            const h = aethelHashVal(k);
            \\            const h2: u8 = @as(u8, @truncate((h >> 57) & 0x7F)) | 0x80;
            \\            var idx: usize = @intCast(h & mask);
            \\            while (true) {
            \\                const slot = c[idx];
            \\                if (slot == 0) return false;
            \\                if (slot == h2 and aethelEqlVal(ks[idx], k)) return true;
            \\                idx = (idx + 1) & mask;
            \\            }
            \\        }
            \\
            \\        pub fn remove(self: *@This(), k: K) bool {
            \\            if (self.cap == 0 or self.len == 0) return false;
            \\            const c = self.ctrl orelse return false;
            \\            const ks = self.keys orelse return false;
            \\            const mask = self.cap - 1;
            \\            const h = aethelHashVal(k);
            \\            const h2: u8 = @as(u8, @truncate((h >> 57) & 0x7F)) | 0x80;
            \\            var idx: usize = @intCast(h & mask);
            \\            while (true) {
            \\                const slot = c[idx];
            \\                if (slot == 0) return false;
            \\                if (slot == h2 and aethelEqlVal(ks[idx], k)) {
            \\                    c[idx] = 1;
            \\                    self.len -= 1;
            \\                    return true;
            \\                }
            \\                idx = (idx + 1) & mask;
            \\            }
            \\        }
            \\
            \\        pub fn clear(self: *@This()) void {
            \\            if (self.cap > 0) {
            \\                if (self.ctrl) |c| @memset(c[0..self.cap], 0);
            \\            }
            \\            self.len = 0;
            \\            self.used = 0;
            \\        }
            \\
            \\        pub fn deinit(self: @This()) void {
            \\            if (self.cap > 0) {
            \\                if (self.ctrl) |c| aethel_gpa.free(c[0..self.cap]);
            \\                if (self.keys) |ks| aethel_gpa.free(ks[0..self.cap]);
            \\            }
            \\        }
            \\    };
            \\}
            \\
            \\fn AethelDeque(comptime T: type) type {
            \\    return struct {
            \\        buf: ?[*]T = null,
            \\        head: usize = 0,
            \\        len: usize = 0,
            \\        cap: usize = 0,
            \\
            \\        pub fn new() @This() {
            \\            return .{};
            \\        }
            \\
            \\        pub fn withCapacity(req_cap: u64) @This() {
            \\            var self = @This(){};
            \\            if (req_cap > 0) self.ensureCap(@intCast(req_cap));
            \\            return self;
            \\        }
            \\
            \\        fn ensureCap(self: *@This(), min_cap: usize) void {
            \\            if (min_cap <= self.cap) return;
            \\            var new_cap: usize = if (self.cap == 0) 8 else self.cap * 2;
            \\            while (new_cap < min_cap) new_cap *= 2;
            \\            const new_buf = aethel_gpa.alloc(T, new_cap) catch @panic("aethel: out of memory");
            \\            if (self.buf) |old_p| {
            \\                const mask = self.cap - 1;
            \\                for (0..self.len) |i| {
            \\                    new_buf[i] = old_p[(self.head + i) & mask];
            \\                }
            \\                if (self.cap > 0) aethel_gpa.free(old_p[0..self.cap]);
            \\            }
            \\            self.buf = new_buf.ptr;
            \\            self.head = 0;
            \\            self.cap = new_cap;
            \\        }
            \\
            \\        pub fn pushBack(self: *@This(), val: T) void {
            \\            if (self.len == self.cap) self.ensureCap(self.len + 1);
            \\            const p = self.buf.?;
            \\            const idx = (self.head + self.len) & (self.cap - 1);
            \\            p[idx] = val;
            \\            self.len += 1;
            \\        }
            \\
            \\        pub fn pushFront(self: *@This(), val: T) void {
            \\            if (self.len == self.cap) self.ensureCap(self.len + 1);
            \\            const p = self.buf.?;
            \\            self.head = (self.head + self.cap - 1) & (self.cap - 1);
            \\            p[self.head] = val;
            \\            self.len += 1;
            \\        }
            \\
            \\        pub fn popFront(self: *@This()) ?T {
            \\            if (self.len == 0) return null;
            \\            const p = self.buf orelse return null;
            \\            const v = p[self.head];
            \\            self.head = (self.head + 1) & (self.cap - 1);
            \\            self.len -= 1;
            \\            return v;
            \\        }
            \\
            \\        pub fn popBack(self: *@This()) ?T {
            \\            if (self.len == 0) return null;
            \\            const p = self.buf orelse return null;
            \\            self.len -= 1;
            \\            const idx = (self.head + self.len) & (self.cap - 1);
            \\            return p[idx];
            \\        }
            \\
            \\        pub fn get(self: @This(), idx: u64) ?T {
            \\            const i: usize = @intCast(idx);
            \\            if (i >= self.len) return null;
            \\            const p = self.buf orelse return null;
            \\            return p[(self.head + i) & (self.cap - 1)];
            \\        }
            \\
            \\        pub fn clear(self: *@This()) void {
            \\            self.head = 0;
            \\            self.len = 0;
            \\        }
            \\
            \\        pub fn deinit(self: @This()) void {
            \\            if (self.cap > 0) {
            \\                if (self.buf) |p| aethel_gpa.free(p[0..self.cap]);
            \\            }
            \\        }
            \\    };
            \\}
            \\
            \\
        );
    }

    fn emitSliceIndexExpr(self: *Emitter, expr: *const ast.Expr) Io.Writer.Error!void {
        if (self.isUnsizedIntLit(expr)) |lit| {
            if (!lit.negative) {
                try self.w.print("{d}", .{lit.mag});
                return;
            }
        }
        try self.w.writeAll("@as(usize, @intCast(");
        try self.emitExpr(expr);
        try self.w.writeAll("))");
    }

    fn emitIdent(self: *Emitter, name: []const u8) Io.Writer.Error!void {
        if (isZigKeyword(name)) {
            try self.w.print("@\"{s}\"", .{name});
        } else {
            try self.w.writeAll(name);
        }
    }

    fn emitTy(self: *Emitter, ty: *const sema.Ty) Io.Writer.Error!void {
        switch (ty.*) {
            .int => |it| try self.w.print("{c}{d}", .{ if (it.signed) @as(u8, 'i') else @as(u8, 'u'), it.bits }),
            .int_range => |ir| try self.w.print("{c}{d}", .{
                if (ir.synthesized.signed) @as(u8, 'i') else @as(u8, 'u'),
                ir.synthesized.bits,
            }),
            .f32 => try self.w.writeAll("f32"),
            .f64 => try self.w.writeAll("f64"),
            .bool => try self.w.writeAll("bool"),
            .string => try self.w.writeAll("[]const u8"),
            .unit, .err => try self.w.writeAll("void"),
            .record => |ridx| {
                if (ridx < self.checked.records.len) {
                    try self.emitIdent(self.checked.records[ridx].name);
                } else {
                    try self.w.writeAll("void");
                }
            },
            .adt => |aidx| {
                if (aidx < self.checked.adts.len) {
                    try self.emitIdent(self.checked.adts[aidx].name);
                } else {
                    try self.w.writeAll("void");
                }
            },
            .opaque_ty => try self.w.writeAll("?*anyopaque"),
            .slice => |sl| {
                if (sl.mutable) {
                    try self.w.writeAll("[]");
                } else {
                    try self.w.writeAll("[]const ");
                }
                try self.emitTy(sl.elem);
            },
            .collection => |c| {
                if (c.elem_record) |ridx| {
                    if (ridx < self.checked.records.len) {
                        const rec = &self.checked.records[ridx];
                        switch (recordBackingKind(rec)) {
                            .soa => {
                                try self.w.print("__AethelSoA_{s}", .{rec.name});
                                return;
                            },
                            .aosoa => |w| {
                                try self.w.print("__AethelAoSoA_{d}_{s}", .{ w, rec.name });
                                return;
                            },
                            .aos_slice => {},
                        }
                    }
                }
                try self.w.writeAll("[]");
                try self.emitTy(c.elem_ty);
            },
            .vec => |v| {
                if (v.elem_record) |ridx| {
                    if (ridx < self.checked.records.len) {
                        const rec = &self.checked.records[ridx];
                        switch (recordBackingKind(rec)) {
                            .soa => {
                                try self.w.print("__AethelDynSoA_{s}", .{rec.name});
                                return;
                            },
                            .aosoa => |w| {
                                try self.w.print("__AethelDynAoSoA_{d}_{s}", .{ w, rec.name });
                                return;
                            },
                            .aos_slice => {},
                        }
                    }
                }
                try self.w.writeAll("AethelVec(");
                try self.emitTy(v.elem_ty);
                try self.w.writeByte(')');
            },
            .map => |m| {
                try self.w.writeAll("AethelMap(");
                try self.emitTy(m.key_ty);
                try self.w.writeAll(", ");
                try self.emitTy(m.val_ty);
                try self.w.writeByte(')');
            },
            .set => |s| {
                try self.w.writeAll("AethelSet(");
                try self.emitTy(s.elem_ty);
                try self.w.writeByte(')');
            },
            .deque => |d| {
                try self.w.writeAll("AethelDeque(");
                try self.emitTy(d.elem_ty);
                try self.w.writeByte(')');
            },
            .view => |v| {
                if (v.target.* == .collection or v.target.* == .slice) {
                    try self.emitTy(v.target);
                } else if (v.target.* == .opaque_ty) {
                    if (v.mode == .exclusive) {
                        try self.w.writeAll("?*anyopaque");
                    } else {
                        try self.w.writeAll("?*const anyopaque");
                    }
                } else {
                    if (v.mode == .exclusive) {
                        try self.w.writeByte('*');
                    } else {
                        try self.w.writeAll("*const ");
                    }
                    try self.emitTy(v.target);
                }
            },
            .path_borrow => |pb| {
                if (pb.base.* == .collection or pb.base.* == .slice) {
                    try self.emitTy(pb.base);
                } else if (pb.mode != null and pb.mode.? == .shared) {
                    try self.w.writeAll("*const ");
                    try self.emitTy(pb.base);
                } else {
                    try self.w.writeByte('*');
                    try self.emitTy(pb.base);
                }
            },
            .tuple => |elems| {
                if (elems.len == 0) {
                    try self.w.writeAll("void");
                } else {
                    try self.w.writeAll("struct { ");
                    for (elems, 0..) |el, i| {
                        if (i > 0) try self.w.writeAll(", ");
                        try self.emitTy(el);
                    }
                    try self.w.writeAll(" }");
                }
            },
            .option => |inner| {
                try self.w.writeByte('?');
                try self.emitTy(inner);
            },
            .result => |res| {
                try self.w.writeAll("AethelResult(");
                try self.emitTy(res.ok);
                try self.w.writeAll(", ");
                try self.emitTy(res.err);
                try self.w.writeByte(')');
            },
            .fn_ty => |ft| {
                try self.w.writeAll("*const fn (");
                for (ft.params, 0..) |p, i| {
                    if (i > 0) try self.w.writeAll(", ");
                    try self.emitTy(p);
                }
                try self.w.writeAll(") ");
                try self.emitTy(ft.ret);
            },
            .type_var => |tv| try self.w.print("__T_{s}", .{tv}),
            .applied => |ap| {
                const base_name = switch (ap.kind) {
                    .record => self.checked.records[ap.decl_idx].name,
                    .adt => self.checked.adts[ap.decl_idx].name,
                    .opaque_ty => "Opaque",
                };
                try self.emitIdent(base_name);
                if (ap.args.len > 0) {
                    try self.w.writeByte('(');
                    for (ap.args, 0..) |a, ai| {
                        if (ai > 0) try self.w.writeAll(", ");
                        try self.emitTy(a);
                    }
                    try self.w.writeByte(')');
                }
            },
            .hkt_app => |ha| {
                try self.w.print("__F_{s}(", .{ha.ctor});
                try self.emitTy(ha.arg);
                try self.w.writeByte(')');
            },
        }
    }

    fn emitAstType(self: *Emitter, ty_ast: *const ast.TypeExpr) Io.Writer.Error!void {
        switch (ty_ast.*) {
            .primitive => |p| switch (p.prim) {
                .unsigned => |bits| try self.w.print("u{d}", .{bits}),
                .signed => |bits| try self.w.print("i{d}", .{bits}),
                .f32 => try self.w.writeAll("f32"),
                .f64 => try self.w.writeAll("f64"),
                .bool => try self.w.writeAll("bool"),
            },
            .named => |n| {
                if (n.path.len > 0) {
                    const head = self.sourceOf(n.path[n.path.len - 1]);
                    if (std.mem.eql(u8, head, "String")) {
                        try self.w.writeAll("[]const u8");
                    } else if (std.mem.eql(u8, head, "Option") and n.args.len > 0) {
                        try self.w.writeByte('?');
                        try self.emitAstType(n.args[0]);
                    } else if (std.mem.eql(u8, head, "Result") and n.args.len >= 2) {
                        try self.w.writeAll("AethelResult(");
                        try self.emitAstType(n.args[0]);
                        try self.w.writeAll(", ");
                        try self.emitAstType(n.args[1]);
                        try self.w.writeByte(')');
                    } else {
                        try self.emitIdent(head);
                    }
                } else {
                    try self.w.writeAll("void");
                }
            },
            .type_var => |tv| try self.w.print("__T_{s}", .{self.sourceOf(tv.name)}),
            .slice => |sl| {
                try self.w.writeAll(if (sl.mutable) "[]" else "[]const ");
                try self.emitAstType(sl.elem);
            },
            .tuple => |tp| {
                if (tp.elems.len == 0) {
                    try self.w.writeAll("void");
                } else {
                    try self.w.writeAll("struct { ");
                    for (tp.elems, 0..) |el, i| {
                        if (i > 0) try self.w.writeAll(", ");
                        try self.emitAstType(el);
                    }
                    try self.w.writeAll(" }");
                }
            },
            else => try self.w.writeAll("void"),
        }
    }

    fn isPureEnumADT(adt: *const sema.CheckedADT) bool {
        for (adt.variants) |v| {
            if (v.field_types.len > 0) return false;
        }
        return true;
    }

    fn isCompactPackedADT(adt: *const sema.CheckedADT) bool {
        if (isPureEnumADT(adt)) return false;
        if (adt.adt_layout.tag_bits == 0 or adt.adt_layout.max_payload_bits == 0) return false;
        if (adt.adt_layout.total_bits > 8) return false;
        for (adt.variants) |v| {
            if (v.field_types.len > 1) return false;
            if (v.field_types.len == 1) {
                const ft = v.field_types[0];
                if (ft.* != .bool and ft.isInteger() == null) return false;
            }
        }
        return true;
    }

    fn recordBinCount(rec: *const sema.CheckedRecord, byte_off: usize) usize {
        var count: usize = 0;
        for (rec.record_layout.fields) |fp| {
            if (fp.bit_offset != null and fp.byte_offset == byte_off) count += 1;
        }
        return count;
    }

    fn fieldBinByte(rec: *const sema.CheckedRecord, fidx: usize) ?usize {
        if (fidx >= rec.record_layout.fields.len) return null;
        const fp = rec.record_layout.fields[fidx];
        if (fp.bit_offset != null and recordBinCount(rec, fp.byte_offset) >= 2) {
            return fp.byte_offset;
        }
        return null;
    }

    fn recordHasAnyBin(rec: *const sema.CheckedRecord) bool {
        for (0..rec.fields.len) |fi| {
            if (fieldBinByte(rec, fi) != null) return true;
        }
        return false;
    }

    const BackingKind = union(enum) {
        aos_slice,
        soa,
        aosoa: usize,
    };

    fn recordBackingKind(rec: *const sema.CheckedRecord) BackingKind {
        if (rec.fields.len == 0 or recordHasAnyBin(rec)) return .aos_slice;
        if (rec.collection_layout) |cl| {
            return switch (cl) {
                .soa => .soa,
                .aosoa => |w| .{ .aosoa = w },
                else => .aos_slice,
            };
        }
        return .aos_slice;
    }

    fn tyBackingKind(self: *const Emitter, ty: ?*const sema.Ty) ?struct { ridx: usize, kind: BackingKind } {
        const t = ty orelse return null;
        const inner: *const sema.Ty = switch (t.*) {
            .view => |v| v.target,
            .path_borrow => |pb| pb.base,
            else => t,
        };
        const ridx = switch (inner.*) {
            .collection => |c| c.elem_record,
            .vec => |v| v.elem_record,
            else => null,
        } orelse return null;
        if (ridx >= self.checked.records.len) return null;
        const bk = recordBackingKind(&self.checked.records[ridx]);
        if (bk == .aos_slice) return null;
        return .{ .ridx = ridx, .kind = bk };
    }

    fn isVecTyOrViewToVec(self: *const Emitter, ty: ?*const sema.Ty) bool {
        _ = self;
        const t = ty orelse return false;
        const inner: *const sema.Ty = switch (t.*) {
            .view => |v| v.target,
            .path_borrow => |pb| pb.base,
            else => t,
        };
        return inner.* == .vec;
    }

    fn recordRecordIdxOfTy(ty: *const sema.Ty) ?usize {
        return switch (ty.*) {
            .record => |ri| ri,
            .applied => |ap| if (ap.kind == .record) ap.decl_idx else null,
            .view => |v| recordRecordIdxOfTy(v.target),
            .path_borrow => |pb| recordRecordIdxOfTy(pb.base),
            else => null,
        };
    }

    fn findRecordFieldIdx(rec: *const sema.CheckedRecord, fname: []const u8) ?usize {
        for (rec.fields, 0..) |cf, fi| {
            if (std.mem.eql(u8, cf.name, fname)) return fi;
        }
        return null;
    }

    fn findCheckedRecordIndex(self: *const Emitter, name: []const u8) ?usize {
        for (self.checked.records, 0..) |r, idx| {
            if (std.mem.eql(u8, r.name, name)) return idx;
        }
        return null;
    }

    fn findCheckedADTIndex(self: *const Emitter, name: []const u8) ?usize {
        for (self.checked.adts, 0..) |a, idx| {
            if (std.mem.eql(u8, a.name, name)) return idx;
        }
        return null;
    }

    fn findCheckedFn(self: *const Emitter, name: []const u8) ?*const sema.CheckedFunction {
        for (self.checked.functions) |*f| {
            if (std.mem.eql(u8, f.name, name)) return f;
        }
        return null;
    }

    fn findCheckedVariant(
        self: *const Emitter,
        adt_name_opt: ?[]const u8,
        var_name: []const u8,
    ) ?struct { aidx: usize, vidx: usize } {
        if (adt_name_opt) |an| {
            if (self.findCheckedADTIndex(an)) |aidx| {
                for (self.checked.adts[aidx].variants, 0..) |v, vidx| {
                    if (std.mem.eql(u8, v.name, var_name)) return .{ .aidx = aidx, .vidx = vidx };
                }
            }
        }
        for (self.checked.adts, 0..) |adt_def, aidx| {
            for (adt_def.variants, 0..) |v, vidx| {
                if (std.mem.eql(u8, v.name, var_name)) return .{ .aidx = aidx, .vidx = vidx };
            }
        }
        return null;
    }

    fn emitBackingHelpers(self: *Emitter, rec: *const sema.CheckedRecord) Io.Writer.Error!void {
        switch (recordBackingKind(rec)) {
            .aos_slice => {},
            .soa => {
                try self.w.print("const __AethelSoA_{s} = struct {{\n", .{rec.name});
                try self.w.writeAll("    len: usize,\n");
                for (rec.fields) |f| {
                    try self.w.writeAll("    ");
                    try self.emitIdent(f.name);
                    try self.w.writeAll(": []");
                    try self.emitTy(f.ty);
                    try self.w.writeAll(",\n");
                }
                try self.w.writeAll("    pub inline fn slice(self: @This(), lo: usize, hi: usize) @This() {\n");
                try self.w.writeAll("        return .{ .len = hi - lo");
                for (rec.fields) |f| {
                    try self.w.writeAll(", .");
                    try self.emitIdent(f.name);
                    try self.w.writeAll(" = self.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll("[lo..hi]");
                }
                try self.w.writeAll(" };\n    }\n");
                try self.w.writeAll("    pub inline fn get(self: @This(), idx: usize) ");
                try self.emitIdent(rec.name);
                try self.w.writeAll(" {\n        return .{ ");
                for (rec.fields, 0..) |f, fi| {
                    if (fi > 0) try self.w.writeAll(", ");
                    try self.w.writeByte('.');
                    try self.emitIdent(f.name);
                    try self.w.writeAll(" = self.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll("[idx]");
                }
                try self.w.writeAll(" };\n    }\n");
                try self.w.writeAll("    pub inline fn set(self: @This(), idx: usize, v: ");
                try self.emitIdent(rec.name);
                try self.w.writeAll(") void {\n");
                for (rec.fields) |f| {
                    try self.w.writeAll("        self.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll("[idx] = v.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll(";\n");
                }
                try self.w.writeAll("    }\n};\n");
                try self.w.print("const __AethelDynSoA_{s} = struct {{\n", .{rec.name});
                try self.w.writeAll("    len: usize = 0,\n    cap: usize = 0,\n");
                for (rec.fields) |f| {
                    try self.w.writeAll("    ");
                    try self.emitIdent(f.name);
                    try self.w.writeAll(": ?[*]align(64) ");
                    try self.emitTy(f.ty);
                    try self.w.writeAll(" = null,\n");
                }
                try self.w.writeAll("    pub fn new() @This() { return .{}; }\n");
                try self.w.writeAll("    pub fn withCapacity(req_cap: u64) @This() {\n        var self = @This(){};\n        if (req_cap > 0) self.ensureExactCap(@intCast(req_cap));\n        return self;\n    }\n");
                try self.w.writeAll("    pub fn fromSlice(src: []const ");
                try self.emitIdent(rec.name);
                try self.w.writeAll(") @This() {\n        var self = @This(){};\n        if (src.len > 0) {\n            self.ensureExactCap(src.len);\n            for (src, 0..) |item, k| self.set(k, item);\n            self.len = src.len;\n        }\n        return self;\n    }\n");
                try self.w.writeAll("    fn allocExactCap(self: *@This(), new_cap: usize) void {\n");
                for (rec.fields, 0..) |f, fi| {
                    try self.w.print("        const __nf_{d} = aethel_gpa.alignedAlloc(", .{fi});
                    try self.emitTy(f.ty);
                    try self.w.writeAll(", .@\"64\", new_cap) catch @panic(\"aethel: out of memory\");\n");
                    try self.w.writeAll("        if (self.");
                    try self.emitIdent(f.name);
                    try self.w.print(") |op| {{ if (self.len > 0) @memcpy(__nf_{d}[0..self.len], op[0..self.len]); if (self.cap > 0) aethel_gpa.free(op[0..self.cap]); }}\n", .{fi});
                    try self.w.writeAll("        self.");
                    try self.emitIdent(f.name);
                    try self.w.print(" = __nf_{d}.ptr;\n", .{fi});
                }
                try self.w.writeAll("        self.cap = new_cap;\n    }\n");
                try self.w.writeAll("    fn ensureExactCap(self: *@This(), exact_cap: usize) void {\n        if (exact_cap <= self.cap) return;\n        self.allocExactCap(exact_cap);\n    }\n");
                try self.w.writeAll("    fn ensureCap(self: *@This(), min_cap: usize) void {\n");
                try self.w.writeAll("        if (min_cap <= self.cap) return;\n");
                try self.w.writeAll("        var new_cap: usize = if (self.cap == 0) 8 else self.cap * 2;\n");
                try self.w.writeAll("        while (new_cap < min_cap) new_cap *= 2;\n");
                try self.w.writeAll("        self.allocExactCap(new_cap);\n    }\n");
                try self.w.writeAll("    pub fn reserve(self: *@This(), additional: u64) void { self.ensureCap(self.len + @as(usize, @intCast(additional))); }\n");
                try self.w.writeAll("    pub fn push(self: *@This(), v: ");
                try self.emitIdent(rec.name);
                try self.w.writeAll(") void {\n        if (self.len == self.cap) self.ensureCap(self.len + 1);\n        self.set(self.len, v);\n        self.len += 1;\n    }\n");
                try self.w.writeAll("    pub fn pop(self: *@This()) ?");
                try self.emitIdent(rec.name);
                try self.w.writeAll(" {\n        if (self.len == 0) return null;\n        self.len -= 1;\n        return self.get(self.len);\n    }\n");
                try self.w.writeAll("    pub inline fn get(self: @This(), idx: usize) ");
                try self.emitIdent(rec.name);
                try self.w.writeAll(" {\n        return .{ ");
                for (rec.fields, 0..) |f, fi| {
                    if (fi > 0) try self.w.writeAll(", ");
                    try self.w.writeByte('.');
                    try self.emitIdent(f.name);
                    try self.w.writeAll(" = self.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll(".?[idx]");
                }
                try self.w.writeAll(" };\n    }\n");
                try self.w.writeAll("    pub fn getOpt(self: @This(), idx: u64) ?");
                try self.emitIdent(rec.name);
                try self.w.writeAll(" {\n        const i: usize = @intCast(idx);\n        if (i >= self.len) return null;\n        return self.get(i);\n    }\n");
                try self.w.writeAll("    pub inline fn set(self: @This(), idx: usize, v: ");
                try self.emitIdent(rec.name);
                try self.w.writeAll(") void {\n");
                for (rec.fields) |f| {
                    try self.w.writeAll("        self.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll(".?[idx] = v.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll(";\n");
                }
                try self.w.writeAll("    }\n");
                try self.w.writeAll("    pub fn setChecked(self: *@This(), idx: u64, v: ");
                try self.emitIdent(rec.name);
                try self.w.writeAll(") bool {\n        const i: usize = @intCast(idx);\n        if (i >= self.len) return false;\n        self.set(i, v);\n        return true;\n    }\n");
                try self.w.writeAll("    pub fn swapRemove(self: *@This(), idx: u64) ?");
                try self.emitIdent(rec.name);
                try self.w.writeAll(" {\n        const i: usize = @intCast(idx);\n        if (i >= self.len) return null;\n        const removed = self.get(i);\n        self.len -= 1;\n        if (i != self.len) self.set(i, self.get(self.len));\n        return removed;\n    }\n");
                try self.w.writeAll("    pub fn clear(self: *@This()) void { self.len = 0; }\n");
                try self.w.print("    pub inline fn asView(self: @This()) __AethelSoA_{s} {{\n        return .{{ .len = self.len", .{rec.name});
                for (rec.fields) |f| {
                    try self.w.writeAll(", .");
                    try self.emitIdent(f.name);
                    try self.w.writeAll(" = if (self.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll(") |p| p[0..self.len] else &.{}");
                }
                try self.w.writeAll(" };\n    }\n");
                try self.w.print("    pub inline fn mutView(self: *@This()) __AethelSoA_{s} {{\n        return self.asView();\n    }}\n", .{rec.name});
                try self.w.print("    pub inline fn slice(self: @This(), lo: usize, hi: usize) __AethelSoA_{s} {{\n        return self.asView().slice(lo, hi);\n    }}\n", .{rec.name});
                try self.w.writeAll("    pub fn deinit(self: @This()) void {\n        if (self.cap > 0) {\n");
                for (rec.fields) |f| {
                    try self.w.writeAll("            if (self.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll(") |p| aethel_gpa.free(p[0..self.cap]);\n");
                }
                try self.w.writeAll("        }\n    }\n};\n");
            },
            .aosoa => |w| {
                var all_c_abi = true;
                for (rec.fields) |f| {
                    const ok = switch (f.ty.*) {
                        .int => |it| it.bits >= 8 and std.math.isPowerOfTwo(it.bits),
                        .int_range => |ir| ir.synthesized.bits >= 8 and std.math.isPowerOfTwo(ir.synthesized.bits),
                        .f32, .f64 => true,
                        .record => true,
                        else => false,
                    };
                    if (!ok) {
                        all_c_abi = false;
                        break;
                    }
                }
                try self.w.print("const __AethelTile_{d}_{s} = {s} {{\n", .{
                    w,
                    rec.name,
                    if (all_c_abi) "extern struct" else "struct",
                });
                for (rec.fields, 0..) |f, fi| {
                    try self.w.writeAll("    ");
                    try self.emitIdent(f.name);
                    try self.w.print(": [{d}]", .{w});
                    try self.emitTy(f.ty);
                    try self.w.writeAll(if (fi == 0) " align(64),\n" else ",\n");
                }
                try self.w.writeAll("};\n");
                try self.w.print("const __AethelAoSoA_{d}_{s} = struct {{\n", .{ w, rec.name });
                try self.w.print("    tiles: []__AethelTile_{d}_{s},\n", .{ w, rec.name });
                try self.w.writeAll("    base_elem: usize = 0,\n");
                try self.w.writeAll("    len: usize,\n");
                try self.w.writeAll("    pub inline fn slice(self: @This(), lo: usize, hi: usize) @This() {\n");
                try self.w.writeAll("        return .{ .tiles = self.tiles, .base_elem = self.base_elem + lo, .len = hi - lo };\n    }\n");
                try self.w.writeAll("    pub inline fn get(self: @This(), idx: usize) ");
                try self.emitIdent(rec.name);
                try self.w.writeAll(" {\n        const __a = self.base_elem + idx;\n");
                try self.w.print("        const __t = &self.tiles[__a / {d}];\n", .{w});
                try self.w.print("        const __l = __a % {d};\n", .{w});
                try self.w.writeAll("        return .{ ");
                for (rec.fields, 0..) |f, fi| {
                    if (fi > 0) try self.w.writeAll(", ");
                    try self.w.writeByte('.');
                    try self.emitIdent(f.name);
                    try self.w.writeAll(" = __t.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll("[__l]");
                }
                try self.w.writeAll(" };\n    }\n");
                try self.w.writeAll("    pub inline fn set(self: @This(), idx: usize, v: ");
                try self.emitIdent(rec.name);
                try self.w.writeAll(") void {\n        const __a = self.base_elem + idx;\n");
                try self.w.print("        const __t = &self.tiles[__a / {d}];\n", .{w});
                try self.w.print("        const __l = __a % {d};\n", .{w});
                for (rec.fields) |f| {
                    try self.w.writeAll("        __t.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll("[__l] = v.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll(";\n");
                }
                try self.w.writeAll("    }\n};\n");
                try self.w.print("const __AethelDynAoSoA_{d}_{s} = struct {{\n", .{ w, rec.name });
                try self.w.print("    tiles: ?[*]__AethelTile_{d}_{s} = null,\n", .{ w, rec.name });
                try self.w.writeAll("    len: usize = 0,\n    tile_cap: usize = 0,\n");
                try self.w.writeAll("    pub fn new() @This() { return .{}; }\n");
                try self.w.writeAll("    pub fn withCapacity(req_cap: u64) @This() {\n        var self = @This(){};\n");
                try self.w.print("        if (req_cap > 0) self.ensureExactTileCap((@as(usize, @intCast(req_cap)) + {d}) / {d});\n        return self;\n    }}\n", .{ w - 1, w });
                try self.w.writeAll("    pub fn fromSlice(src: []const ");
                try self.emitIdent(rec.name);
                try self.w.writeAll(") @This() {\n        var self = @This(){};\n        if (src.len > 0) {\n");
                try self.w.print("            self.ensureExactTileCap((src.len + {d}) / {d});\n", .{ w - 1, w });
                try self.w.writeAll("            for (src, 0..) |item, k| self.set(k, item);\n            self.len = src.len;\n        }\n        return self;\n    }\n");
                try self.w.writeAll("    fn allocExactTileCap(self: *@This(), new_tc: usize) void {\n");
                try self.w.print("        const new_mem = aethel_gpa.alloc(__AethelTile_{d}_{s}, new_tc) catch @panic(\"aethel: out of memory\");\n", .{ w, rec.name });
                try self.w.writeAll("        if (self.tiles) |old_t| {\n            if (self.tile_cap > 0) {\n                @memcpy(new_mem[0..self.tile_cap], old_t[0..self.tile_cap]);\n                aethel_gpa.free(old_t[0..self.tile_cap]);\n            }\n        }\n");
                try self.w.writeAll("        self.tiles = new_mem.ptr;\n        self.tile_cap = new_tc;\n    }\n");
                try self.w.writeAll("    fn ensureExactTileCap(self: *@This(), exact_tc: usize) void {\n");
                try self.w.writeAll("        if (exact_tc <= self.tile_cap) return;\n");
                try self.w.writeAll("        self.allocExactTileCap(exact_tc);\n    }\n");
                try self.w.writeAll("    fn ensureTileCap(self: *@This(), min_tcap: usize) void {\n");
                try self.w.writeAll("        if (min_tcap <= self.tile_cap) return;\n");
                try self.w.writeAll("        var new_tc: usize = if (self.tile_cap == 0) 1 else self.tile_cap * 2;\n");
                try self.w.writeAll("        while (new_tc < min_tcap) new_tc *= 2;\n");
                try self.w.writeAll("        self.allocExactTileCap(new_tc);\n    }\n");
                try self.w.print("    pub fn reserve(self: *@This(), additional: u64) void {{\n        const need_elems = self.len + @as(usize, @intCast(additional));\n        if (need_elems > 0) self.ensureTileCap((need_elems + {d}) / {d});\n    }}\n", .{ w - 1, w });
                try self.w.writeAll("    pub fn push(self: *@This(), v: ");
                try self.emitIdent(rec.name);
                try self.w.writeAll(") void {\n");
                try self.w.print("        const need_tc = (self.len + 1 + {d}) / {d};\n", .{ w - 1, w });
                try self.w.writeAll("        if (need_tc > self.tile_cap) self.ensureTileCap(need_tc);\n");
                try self.w.writeAll("        self.set(self.len, v);\n        self.len += 1;\n    }\n");
                try self.w.writeAll("    pub fn pop(self: *@This()) ?");
                try self.emitIdent(rec.name);
                try self.w.writeAll(" {\n        if (self.len == 0) return null;\n        self.len -= 1;\n        return self.get(self.len);\n    }\n");
                try self.w.writeAll("    pub inline fn get(self: @This(), idx: usize) ");
                try self.emitIdent(rec.name);
                try self.w.print(" {{\n        const __t = &self.tiles.?[idx / {d}];\n        const __l = idx % {d};\n        return .{{ ", .{ w, w });
                for (rec.fields, 0..) |f, fi| {
                    if (fi > 0) try self.w.writeAll(", ");
                    try self.w.writeByte('.');
                    try self.emitIdent(f.name);
                    try self.w.writeAll(" = __t.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll("[__l]");
                }
                try self.w.writeAll(" };\n    }\n");
                try self.w.writeAll("    pub fn getOpt(self: @This(), idx: u64) ?");
                try self.emitIdent(rec.name);
                try self.w.writeAll(" {\n        const i: usize = @intCast(idx);\n        if (i >= self.len) return null;\n        return self.get(i);\n    }\n");
                try self.w.writeAll("    pub inline fn set(self: @This(), idx: usize, v: ");
                try self.emitIdent(rec.name);
                try self.w.print(") void {{\n        const __t = &self.tiles.?[idx / {d}];\n        const __l = idx % {d};\n", .{ w, w });
                for (rec.fields) |f| {
                    try self.w.writeAll("        __t.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll("[__l] = v.");
                    try self.emitIdent(f.name);
                    try self.w.writeAll(";\n");
                }
                try self.w.writeAll("    }\n");
                try self.w.writeAll("    pub fn setChecked(self: *@This(), idx: u64, v: ");
                try self.emitIdent(rec.name);
                try self.w.writeAll(") bool {\n        const i: usize = @intCast(idx);\n        if (i >= self.len) return false;\n        self.set(i, v);\n        return true;\n    }\n");
                try self.w.writeAll("    pub fn swapRemove(self: *@This(), idx: u64) ?");
                try self.emitIdent(rec.name);
                try self.w.writeAll(" {\n        const i: usize = @intCast(idx);\n        if (i >= self.len) return null;\n        const removed = self.get(i);\n        self.len -= 1;\n        if (i != self.len) self.set(i, self.get(self.len));\n        return removed;\n    }\n");
                try self.w.writeAll("    pub fn clear(self: *@This()) void { self.len = 0; }\n");
                try self.w.print("    pub inline fn asView(self: @This()) __AethelAoSoA_{d}_{s} {{\n        return .{{ .tiles = if (self.tiles) |t| t[0..self.tile_cap] else &.{{}}, .base_elem = 0, .len = self.len }};\n    }}\n", .{ w, rec.name });
                try self.w.print("    pub inline fn mutView(self: *@This()) __AethelAoSoA_{d}_{s} {{\n        return self.asView();\n    }}\n", .{ w, rec.name });
                try self.w.print("    pub inline fn slice(self: @This(), lo: usize, hi: usize) __AethelAoSoA_{d}_{s} {{\n        return self.asView().slice(lo, hi);\n    }}\n", .{ w, rec.name });
                try self.w.writeAll("    pub fn deinit(self: @This()) void {\n        if (self.tile_cap > 0) {\n            if (self.tiles) |t| aethel_gpa.free(t[0..self.tile_cap]);\n        }\n    }\n};\n");
            },
        }
    }

    fn emitTypeDecl(self: *Emitter, decl: *const ast.Decl) Io.Writer.Error!void {
        const td = decl.kind.type_decl;
        const name = self.checked.declCanonicalName(decl.span.start) orelse self.sourceOf(td.name);
        switch (td.body) {
            .record => {
                if (self.findCheckedRecordIndex(name)) |ridx| {
                    const rec = self.checked.records[ridx];
                    if (td.type_params.len > 0) {
                        try self.w.writeAll("fn ");
                        try self.emitIdent(name);
                        try self.w.writeByte('(');
                        for (td.type_params, 0..) |tp, ti| {
                            if (ti > 0) try self.w.writeAll(", ");
                            try self.w.print("comptime __T_{s}: type", .{self.sourceOf(tp)});
                        }
                        try self.w.writeAll(") type {\n    return struct {\n");
                        for (rec.fields) |f| {
                            try self.w.writeAll("        ");
                            try self.emitIdent(f.name);
                            try self.w.writeAll(": ");
                            try self.emitTy(f.ty);
                            try self.w.writeAll(",\n");
                        }
                        try self.w.writeAll("    };\n}\n");
                        return;
                    }
                    try self.w.print("// Aethel verified layout: size={d} align={d} conflicts={d}{s}\n", .{
                        rec.record_layout.size,
                        rec.record_layout.alignment,
                        rec.conflicts.len,
                        if (rec.is_flat_c) " (flat C-ABI)" else "",
                    });
                    const has_bins = !rec.is_flat_c and recordHasAnyBin(&rec);
                    var can_assert_size = has_bins or rec.is_flat_c;
                    for (rec.fields) |f| {
                        switch (f.ty.*) {
                            .int, .int_range, .f32, .f64, .bool => {},
                            .record => |inner_ri| {
                                if (!self.checked.records[inner_ri].is_flat_c) can_assert_size = false;
                            },
                            else => can_assert_size = false,
                        }
                    }
                    // Zig `extern struct` supports fixed-width integers, floats, bool (C99 _Bool), and nested extern structs.
                    const use_extern_struct = rec.is_flat_c;

                    // Order physical fields by layout byte_offset ascending unless @layout(flat).
                    const order: []usize = self.alloc.alloc(usize, rec.fields.len) catch &.{};
                    if (order.len == rec.fields.len) {
                        for (order, 0..) |*slot, i| slot.* = i;
                        if (!rec.is_flat_c) {
                            var a: usize = 0;
                            while (a < order.len) : (a += 1) {
                                var b: usize = a + 1;
                                while (b < order.len) : (b += 1) {
                                    const fa = rec.record_layout.fields[order[a]];
                                    const fb = rec.record_layout.fields[order[b]];
                                    const swap = if (fb.byte_offset != fa.byte_offset)
                                        fb.byte_offset < fa.byte_offset
                                    else
                                        (fb.bit_offset orelse 0) < (fa.bit_offset orelse 0);
                                    if (swap) {
                                        const tmp = order[a];
                                        order[a] = order[b];
                                        order[b] = tmp;
                                    }
                                }
                            }
                        }
                    }

                    var emitted_bins = std.AutoHashMapUnmanaged(usize, void).empty;
                    try self.w.writeAll("const ");
                    try self.emitIdent(name);
                    try self.w.writeAll(if (use_extern_struct) " = extern struct {\n" else " = struct {\n");
                    self.indent += 1;
                    const iter_len = if (order.len == rec.fields.len) order.len else rec.fields.len;
                    for (0..iter_len) |oi| {
                        const fi = if (order.len == rec.fields.len) order[oi] else oi;
                        if (!rec.is_flat_c and fieldBinByte(&rec, fi) != null) {
                            const bbyte = fieldBinByte(&rec, fi).?;
                            if (emitted_bins.contains(bbyte)) continue;
                            emitted_bins.put(self.alloc, bbyte, {}) catch {};
                            try self.writeIndent();
                            try self.w.print("__bin_{d}: packed struct(u8) {{\n", .{bbyte});
                            self.indent += 1;
                            var used_bits: u16 = 0;
                            for (0..iter_len) |oj| {
                                const fj = if (order.len == rec.fields.len) order[oj] else oj;
                                if (fieldBinByte(&rec, fj)) |jb| {
                                    if (jb == bbyte) {
                                        const bf = rec.fields[fj];
                                        const bfp = rec.record_layout.fields[fj];
                                        try self.writeIndent();
                                        try self.emitIdent(bf.name);
                                        try self.w.writeAll(": ");
                                        try self.emitTy(bf.ty);
                                        try self.w.writeAll(",\n");
                                        used_bits += bfp.bits;
                                    }
                                }
                            }
                            if (used_bits < 8) {
                                try self.writeIndent();
                                try self.w.print("__pad: u{d} = 0,\n", .{8 - used_bits});
                            }
                            self.indent -= 1;
                            try self.writeIndent();
                            try self.w.writeAll("},\n");
                        } else {
                            const f = rec.fields[fi];
                            try self.writeIndent();
                            try self.emitIdent(f.name);
                            try self.w.writeAll(": ");
                            try self.emitTy(f.ty);
                            try self.w.writeAll(",\n");
                        }
                    }
                    self.indent -= 1;
                    try self.w.writeAll("};\n");
                    if (can_assert_size) {
                        try self.w.writeAll("comptime {\n");
                        try self.w.writeAll("    if (@sizeOf(");
                        try self.emitIdent(name);
                        if (rec.is_flat_c) {
                            try self.w.print(") != {d}) @compileError(\"flat C-ABI record size mismatch\");\n", .{rec.record_layout.size});
                        } else {
                            try self.w.print(") > {d}) @compileError(\"packed record size exceeds verified layout\");\n", .{rec.record_layout.size});
                        }
                        try self.w.writeAll("}\n");
                    }
                    try self.emitBackingHelpers(&rec);
                }
            },
            .variants => {
                if (self.findCheckedADTIndex(name)) |aidx| {
                    const adt_def = &self.checked.adts[aidx];
                    const pure_enum = isPureEnumADT(adt_def);
                    const compact_packed = isCompactPackedADT(adt_def);
                    try self.w.print("// Aethel compact ADT layout: tag_bits={d} max_payload_bits={d} total_bytes={d}\n", .{
                        adt_def.adt_layout.tag_bits,
                        adt_def.adt_layout.max_payload_bits,
                        adt_def.adt_layout.total_bytes,
                    });
                    if (compact_packed) {
                        try self.w.writeAll("const ");
                        try self.emitIdent(name);
                        try self.w.writeAll(" = packed struct(u8) {\n");
                        self.indent += 1;
                        try self.writeIndent();
                        try self.w.print("pub const Tag = enum(u{d}) {{\n", .{adt_def.adt_layout.tag_bits});
                        self.indent += 1;
                        for (adt_def.variants, 0..) |v, vi| {
                            try self.writeIndent();
                            try self.emitIdent(v.name);
                            try self.w.print(" = {d},\n", .{vi});
                        }
                        self.indent -= 1;
                        try self.writeIndent();
                        try self.w.writeAll("};\n");
                        try self.writeIndent();
                        try self.w.writeAll("tag: Tag,\n");
                        try self.writeIndent();
                        try self.w.print("payload: u{d} = 0,\n", .{adt_def.adt_layout.max_payload_bits});
                        const used_bits: u16 = @intCast(adt_def.adt_layout.tag_bits + adt_def.adt_layout.max_payload_bits);
                        if (used_bits < 8) {
                            try self.writeIndent();
                            try self.w.print("__pad: u{d} = 0,\n", .{8 - used_bits});
                        }
                        self.indent -= 1;
                        try self.w.writeAll("};\n");
                        try self.w.writeAll("comptime {\n");
                        try self.w.writeAll("    if (@sizeOf(");
                        try self.emitIdent(name);
                        try self.w.writeAll(") != 1) @compileError(\"compact ADT must occupy 1 byte\");\n");
                        try self.w.writeAll("}\n");
                    } else {
                        try self.w.writeAll("const ");
                        try self.emitIdent(name);
                        if (pure_enum) {
                            try self.w.writeAll(" = enum {\n");
                        } else {
                            try self.w.writeAll(" = union(enum) {\n");
                        }
                        self.indent += 1;
                        for (adt_def.variants) |v| {
                            try self.writeIndent();
                            try self.emitIdent(v.name);
                            if (!pure_enum) {
                                try self.w.writeAll(": ");
                                if (v.field_types.len == 0) {
                                    try self.w.writeAll("void");
                                } else if (v.field_types.len == 1) {
                                    try self.emitTy(v.field_types[0]);
                                } else {
                                    try self.w.writeAll("struct { ");
                                    for (v.field_types, 0..) |ft, fi| {
                                        if (fi > 0) try self.w.writeAll(", ");
                                        try self.emitTy(ft);
                                    }
                                    try self.w.writeAll(" }");
                                }
                            }
                            try self.w.writeAll(",\n");
                        }
                        self.indent -= 1;
                        try self.w.writeAll("};\n");
                    }
                }
            },
            .alias => |ty_ast| {
                try self.w.writeAll("const ");
                try self.emitIdent(name);
                try self.w.writeAll(" = ");
                if (self.checked.aliasType(name)) |aty| {
                    if (aty.* != .err) {
                        try self.emitTy(aty);
                    } else {
                        try self.emitAstType(ty_ast);
                    }
                } else {
                    try self.emitAstType(ty_ast);
                }
                try self.w.writeAll(";\n");
            },
            .empty => {
                try self.w.writeAll("const ");
                try self.emitIdent(name);
                try self.w.writeAll(" = ?*anyopaque;\n");
            },
        }
    }

    fn emitConstDecl(self: *Emitter, decl: *const ast.Decl) Io.Writer.Error!void {
        const cd = decl.kind.const_decl;
        const cname = self.checked.declCanonicalName(decl.span.start) orelse self.sourceOf(cd.name);
        const cty = self.checked.constType(cname);
        try self.w.writeAll("const ");
        try self.emitIdent(cname);
        if (cty) |ty| {
            if (ty.* != .err) {
                try self.w.writeAll(": ");
                try self.emitTy(ty);
            }
        }
        try self.w.writeAll(" = ");
        if (cty) |ty| {
            try self.emitCoercedExpr(cd.value, ty);
        } else {
            try self.emitExpr(cd.value);
        }
        try self.w.writeAll(";\n");
    }

    fn emitExternDecl(self: *Emitter, decl: *const ast.Decl) Io.Writer.Error!void {
        const ex = decl.kind.extern_decl;
        const abi_slice = self.sourceOf(ex.abi);
        try self.w.print("// extern {s} C-ABI declarations\n", .{abi_slice});
        for (ex.fns) |ef| {
            const fname = self.sourceOf(ef.name);
            const cf = self.findCheckedFn(fname);
            try self.w.writeAll("extern \"c\" fn ");
            try self.emitIdent(fname);
            try self.w.writeByte('(');
            var first = true;
            for (ef.params, 0..) |p, pi| {
                const pty_resolved: ?*const sema.Ty = if (cf != null and pi < cf.?.param_types.len) cf.?.param_types[pi] else null;
                if (pty_resolved != null and (pty_resolved.?.* == .slice or (pty_resolved.?.* == .view and pty_resolved.?.view.target.* == .slice))) {
                    const ExternSliceInfo = struct { mutable: bool, elem: *const sema.Ty };
                    const sl: ExternSliceInfo = if (pty_resolved.?.* == .slice)
                        .{ .mutable = pty_resolved.?.slice.mutable, .elem = pty_resolved.?.slice.elem }
                    else
                        .{ .mutable = pty_resolved.?.view.mode == .exclusive and pty_resolved.?.view.target.slice.mutable, .elem = pty_resolved.?.view.target.slice.elem };
                    if (!first) try self.w.writeAll(", ");
                    first = false;
                    try self.emitIdent(self.sourceOf(p.name));
                    try self.w.writeAll("_ptr: [*]");
                    if (!sl.mutable) try self.w.writeAll("const ");
                    try self.emitTy(sl.elem);
                    try self.w.writeAll(", ");
                    try self.emitIdent(self.sourceOf(p.name));
                    try self.w.writeAll("_len: usize");
                    continue;
                }
                if (p.ty) |pty| {
                    if (pty.* == .slice) {
                        if (!first) try self.w.writeAll(", ");
                        first = false;
                        try self.emitIdent(self.sourceOf(p.name));
                        try self.w.writeAll("_ptr: [*]");
                        if (!pty.slice.mutable) try self.w.writeAll("const ");
                        try self.emitAstType(pty.slice.elem);
                        try self.w.writeAll(", ");
                        try self.emitIdent(self.sourceOf(p.name));
                        try self.w.writeAll("_len: usize");
                        continue;
                    }
                }
                if (!first) try self.w.writeAll(", ");
                first = false;
                try self.emitIdent(self.sourceOf(p.name));
                try self.w.writeAll(": ");
                if (pty_resolved != null and pty_resolved.?.* != .err) {
                    try self.emitTy(pty_resolved.?);
                } else if (p.ty) |pty| {
                    try self.emitAstType(pty);
                } else {
                    try self.w.writeAll("usize");
                }
            }
            try self.w.writeAll(") ");
            if (cf != null and cf.?.ret_type.* != .err) {
                try self.emitTy(cf.?.ret_type);
            } else if (ef.ret) |ret| {
                try self.emitAstType(ret);
            } else {
                try self.w.writeAll("void");
            }
            try self.w.writeAll(";\n");
        }
        try self.w.writeByte('\n');
    }

    fn isPointerType(ty: *const sema.Ty) bool {
        if (ty.* == .path_borrow) {
            return ty.path_borrow.base.* != .collection and ty.path_borrow.base.* != .slice and ty.path_borrow.base.* != .opaque_ty;
        }
        if (ty.* == .view) {
            return ty.view.target.* != .collection and ty.view.target.* != .slice and ty.view.target.* != .opaque_ty;
        }
        return false;
    }

    fn findPathBorrowFieldIndices(
        self: *const Emitter,
        ridx: usize,
        pb_ty: *const sema.Ty,
    ) []const usize {
        const rec = &self.checked.records[ridx];
        var list: std.ArrayList(usize) = .empty;
        if (pb_ty.* == .path_borrow) {
            for (pb_ty.path_borrow.paths) |fp| {
                if (fp.len == 0) continue;
                const fnm = self.sourceOf(fp[0]);
                if (findRecordFieldIdx(rec, fnm)) |fi| {
                    var dup = false;
                    for (list.items) |prev| if (prev == fi) {
                        dup = true;
                    };
                    if (!dup) list.append(self.alloc, fi) catch {};
                }
            }
        }
        if (list.items.len == 0) {
            for (0..rec.fields.len) |fi| list.append(self.alloc, fi) catch {};
        }
        return list.toOwnedSlice(self.alloc) catch &.{};
    }

    fn emitCallbackCAbiFnPtrTy(self: *Emitter, ft: sema.FnTy) Io.Writer.Error!void {
        try self.w.writeAll("*const fn (");
        var first = true;
        for (ft.params) |p| {
            if (!first) try self.w.writeAll(", ");
            first = false;
            if (p.* == .string) {
                try self.w.writeAll("noalias [*]const u8, usize");
            } else if (p.* == .slice or (p.* == .view and p.view.target.* == .slice)) {
                const mutable = if (p.* == .slice) p.slice.mutable else (p.view.mode == .exclusive and p.view.target.slice.mutable);
                const elem = if (p.* == .slice) p.slice.elem else p.view.target.slice.elem;
                try self.w.writeAll("noalias [*]");
                if (!mutable) try self.w.writeAll("const ");
                try self.emitTy(elem);
                try self.w.writeAll(", usize");
            } else {
                try self.emitTy(p);
            }
        }
        try self.w.writeAll(") callconv(.c) ");
        if (isVoidTy(ft.ret)) {
            try self.w.writeAll("void");
        } else {
            try self.emitTy(ft.ret);
        }
    }

    fn emitCAbiParamSignature(
        self: *Emitter,
        pname: []const u8,
        pty: *const sema.Ty,
        first: *bool,
    ) Io.Writer.Error!void {
        if (pty.* == .string) {
            if (!first.*) try self.w.writeAll(", ");
            first.* = false;
            try self.emitIdent(pname);
            try self.w.writeAll("_ptr: [*]const u8, ");
            try self.emitIdent(pname);
            try self.w.writeAll("_len: usize");
            return;
        }
        if (pty.* == .fn_ty) {
            if (!first.*) try self.w.writeAll(", ");
            first.* = false;
            try self.emitIdent(pname);
            try self.w.writeAll("_cb: ");
            try self.emitCallbackCAbiFnPtrTy(pty.fn_ty);
            return;
        }
        if (pty.* == .slice or (pty.* == .view and pty.view.target.* == .slice)) {
            const mutable = if (pty.* == .slice) pty.slice.mutable else (pty.view.mode == .exclusive and pty.view.target.slice.mutable);
            const elem = if (pty.* == .slice) pty.slice.elem else pty.view.target.slice.elem;
            if (!first.*) try self.w.writeAll(", ");
            first.* = false;
            try self.emitIdent(pname);
            try self.w.writeAll("_ptr: [*]");
            if (!mutable) try self.w.writeAll("const ");
            try self.emitTy(elem);
            try self.w.writeAll(", ");
            try self.emitIdent(pname);
            try self.w.writeAll("_len: usize");
            return;
        }
        if (self.tyBackingKind(pty)) |bk| {
            const rec = &self.checked.records[bk.ridx];
            switch (bk.kind) {
                .soa => {
                    const fidxs = self.findPathBorrowFieldIndices(bk.ridx, pty);
                    const is_mut = switch (pty.*) {
                        .path_borrow => |pb| pb.mode == null or pb.mode.? == .exclusive,
                        .view => |v| v.mode == .exclusive,
                        .collection => true,
                        else => false,
                    };
                    for (fidxs) |fi| {
                        const f = rec.fields[fi];
                        if (!first.*) try self.w.writeAll(", ");
                        first.* = false;
                        try self.w.print("{s}_{s}_ptr: [*]{s}", .{ pname, f.name, if (is_mut) "" else "const " });
                        try self.emitTy(f.ty);
                    }
                    if (!first.*) try self.w.writeAll(", ");
                    first.* = false;
                    try self.w.print("{s}_len: usize", .{pname});
                    return;
                },
                .aosoa => |w| {
                    const is_mut = switch (pty.*) {
                        .path_borrow => |pb| pb.mode == null or pb.mode.? == .exclusive,
                        .view => |v| v.mode == .exclusive,
                        .collection => true,
                        else => false,
                    };
                    if (!first.*) try self.w.writeAll(", ");
                    first.* = false;
                    try self.w.print("{s}_tiles: [*]{s}__AethelTile_{d}_{s}, {s}_base: usize, {s}_len: usize", .{
                        pname,
                        if (is_mut) "" else "const ",
                        w,
                        rec.name,
                        pname,
                        pname,
                    });
                    return;
                },
                .aos_slice => {},
            }
        }
        if (!first.*) try self.w.writeAll(", ");
        first.* = false;
        try self.emitIdent(pname);
        try self.w.writeAll(": ");
        try self.emitTy(pty);
    }

    fn emitExternalFnProto(self: *Emitter, decl: *const ast.Decl) Io.Writer.Error!void {
        const fd = decl.kind.fn_decl;
        const fname = self.checked.declCanonicalName(decl.span.start) orelse self.sourceOf(fd.name);
        const cf = self.findCheckedFn(fname) orelse return;
        const ext_sym = cf.rust_sym orelse fname;
        try self.w.print("// @external(rust) {s} -> {s}\n", .{ fname, ext_sym });
        try self.w.writeAll("extern \"c\" fn ");
        try self.emitIdent(ext_sym);
        try self.w.writeByte('(');
        var first = true;
        for (fd.params, 0..) |p, pi| {
            const pty = if (pi < cf.param_types.len) cf.param_types[pi] else continue;
            try self.emitCAbiParamSignature(self.sourceOf(p.name), pty, &first);
        }
        try self.w.writeAll(") ");
        try self.emitTy(cf.ret_type);
        try self.w.writeAll(";\n\n");
    }

    fn emitInstanceDecl(self: *Emitter, inst: *const sema.CheckedInstance) Io.Writer.Error!void {
        if (inst.is_external_rust) {
            for (inst.methods) |cm| {
                const esym = cm.ext_sym orelse continue;
                try self.w.writeAll("extern \"c\" fn ");
                try self.emitIdent(esym);
                try self.w.writeByte('(');
                var first = true;
                for (cm.params, 0..) |pt, pi| {
                    const pname = if (cm.ast_method != null and pi < cm.ast_method.?.params.len)
                        self.sourceOf(cm.ast_method.?.params[pi].name)
                    else
                        "arg";
                    try self.emitCAbiParamSignature(pname, pt, &first);
                }
                try self.w.writeAll(") ");
                try self.emitTy(cm.ret);
                try self.w.writeAll(";\n");
            }
        }

        const is_generic = inst.type_params.len > 0 or inst.hkt_params.len > 0 or inst.constraints.len > 0;
        var struct_buf: Io.Writer.Allocating = .init(self.alloc);
        const outer_w = self.w;
        if (is_generic) {
            try outer_w.print("fn __Inst_{s}(", .{inst.name});
            var comma = false;
            for (inst.type_params) |tp| {
                if (comma) try outer_w.writeAll(", ");
                comma = true;
                try outer_w.print("comptime __T_{s}: type", .{tp});
            }
            for (inst.hkt_params) |hp| {
                if (comma) try outer_w.writeAll(", ");
                comma = true;
                try outer_w.print("comptime __F_{s}: fn (comptime type) type", .{hp});
            }
            for (0..inst.constraints.len) |ci| {
                if (comma) try outer_w.writeAll(", ");
                comma = true;
                try outer_w.print("comptime __W_{d}: type", .{ci});
            }
            try outer_w.writeAll(") type {\n");
            self.w = &struct_buf.writer;
            try self.w.writeAll("    return struct {\n        const __InstSelf = @This();\n");
            self.indent += 2;
        } else {
            try self.w.print("const __Inst_{s} = struct {{\n    const __InstSelf = @This();\n", .{inst.name});
            self.indent += 1;
        }

        for (inst.methods) |cm| {
            try self.writeIndent();
            try self.w.writeAll("pub fn ");
            try self.emitIdent(cm.local_name);
            try self.w.writeByte('(');
            var comma = false;
            for (cm.type_params) |tp| {
                if (comma) try self.w.writeAll(", ");
                comma = true;
                try self.w.print("comptime __T_{s}: type", .{tp});
            }
            const method_saved_w = self.w;
            var msig_buf: Io.Writer.Allocating = .init(self.alloc);
            self.w = &msig_buf.writer;
            if (cm.synth == .monad_map or cm.synth == .monad_ap) {
                for (cm.params, 0..) |pt, pi| {
                    if (comma) try self.w.writeAll(", ");
                    comma = true;
                    try self.w.print("arg{d}: ", .{pi});
                    if (pt.* == .fn_ty) try self.w.writeAll("anytype") else try self.emitTy(pt);
                }
                try self.w.writeAll(") ");
                try self.emitTy(cm.ret);
                try self.w.writeAll(" {\n");
                self.indent += 1;
                try self.writeIndent();
                if (cm.synth == .monad_map) {
                    try self.w.print("return __InstSelf.bind(", .{});
                    if (cm.type_params.len >= 2) {
                        try self.w.print("__T_{s}, __T_{s}, ", .{ cm.type_params[0], cm.type_params[1] });
                    }
                    try self.w.writeAll("arg0, struct { f_cb: @TypeOf(arg1), pub fn call(s: @This(), x: ");
                    if (cm.type_params.len >= 1) try self.w.print("__T_{s}", .{cm.type_params[0]}) else try self.w.writeAll("anytype");
                    try self.w.writeAll(") ");
                    try self.emitTy(cm.ret);
                    try self.w.writeAll(" { return __InstSelf.pure(");
                    if (cm.type_params.len >= 2) try self.w.print("__T_{s}, ", .{cm.type_params[1]}) else if (cm.type_params.len >= 1) try self.w.print("__T_{s}, ", .{cm.type_params[0]});
                    try self.w.writeAll("aethelCall(s.f_cb, .{ x })); } }{ .f_cb = arg1 });\n");
                } else {
                    try self.w.writeAll("return __InstSelf.bind(");
                    if (cm.type_params.len >= 2) {
                        try self.w.print("__T_{s}, __T_{s}, ", .{ cm.type_params[0], cm.type_params[1] });
                    }
                    try self.w.writeAll("arg0, struct { mx_val: @TypeOf(arg1), pub fn call(s: @This(), f_fn: anytype) ");
                    try self.emitTy(cm.ret);
                    try self.w.writeAll(" { return __InstSelf.fmap(");
                    if (cm.type_params.len >= 2) try self.w.print("__T_{s}, __T_{s}, ", .{ cm.type_params[0], cm.type_params[1] });
                    try self.w.writeAll("s.mx_val, f_fn); } }{ .mx_val = arg1 });\n");
                }
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("}\n");
                self.w = method_saved_w;
                try self.w.writeAll(msig_buf.written());
                continue;
            }
            for (cm.params, 0..) |pt, pi| {
                if (comma) try self.w.writeAll(", ");
                comma = true;
                const pname = if (cm.ast_method != null and pi < cm.ast_method.?.params.len)
                    self.sourceOf(cm.ast_method.?.params[pi].name)
                else
                    std.fmt.allocPrint(self.alloc, "arg{d}", .{pi}) catch "arg";
                try self.emitIdent(pname);
                try self.w.writeAll(": ");
                if (pt.* == .fn_ty) try self.w.writeAll("anytype") else try self.emitTy(pt);
            }
            try self.w.writeAll(") ");
            try self.emitTy(cm.ret);
            try self.w.writeAll(" {\n");
            self.indent += 1;

            var mbody_buf: Io.Writer.Allocating = .init(self.alloc);
            self.w = &mbody_buf.writer;
            if (cm.ext_sym) |esym| {
                try self.writeIndent();
                if (!isVoidTy(cm.ret)) try self.w.writeAll("return ");
                try self.emitIdent(esym);
                try self.w.writeByte('(');
                for (cm.params, 0..) |_, pi| {
                    if (pi > 0) try self.w.writeAll(", ");
                    const pname = if (cm.ast_method != null and pi < cm.ast_method.?.params.len)
                        self.sourceOf(cm.ast_method.?.params[pi].name)
                    else
                        std.fmt.allocPrint(self.alloc, "arg{d}", .{pi}) catch "arg";
                    try self.emitIdent(pname);
                }
                try self.w.writeAll(");\n");
            } else if (cm.ast_method) |im| {
                const prev_ret = self.current_fn_ret;
                self.current_fn_ret = cm.ret;
                defer self.current_fn_ret = prev_ret;
                const sv_mark = self.pushScopeVars();
                defer self.popScopeVars(sv_mark);
                for (im.params, 0..) |p, pi| {
                    const pn = self.sourceOf(p.name);
                    const pty: ?*const sema.Ty = if (pi < cm.params.len) cm.params[pi] else null;
                    self.bindScopeVar(pn, pty, false);
                    if (!self.blockMentionsIdent(&im.body, pn)) {
                        try self.writeIndent();
                        try self.w.writeAll("_ = ");
                        try self.emitIdent(pn);
                        try self.w.writeAll(";\n");
                    }
                }
                try self.emitStmtsWithRest(im.body.stmts, im.body.tail);
                if (im.body.tail) |tail| {
                    if (isVoidTy(cm.ret)) {
                        try self.emitTailStmt(tail);
                    } else {
                        try self.writeIndent();
                        try self.w.writeAll("return ");
                        try self.emitCoercedExpr(tail, cm.ret);
                        try self.w.writeAll(";\n");
                    }
                }
            }
            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeAll("}\n");

            self.w = method_saved_w;
            try self.w.writeAll(msig_buf.written());
            for (cm.type_params) |tp| {
                const tsym = std.fmt.allocPrint(self.alloc, "__T_{s}", .{tp}) catch continue;
                if (std.mem.indexOf(u8, msig_buf.written(), tsym) == null and
                    std.mem.indexOf(u8, mbody_buf.written(), tsym) == null)
                {
                    try self.writeIndent();
                    try self.w.print("    _ = {s};\n", .{tsym});
                }
            }
            try self.w.writeAll(mbody_buf.written());
        }

        if (is_generic) {
            self.indent -= 2;
            self.w = outer_w;
            const sbody = struct_buf.written();
            for (inst.type_params) |tp| {
                const tsym = std.fmt.allocPrint(self.alloc, "__T_{s}", .{tp}) catch continue;
                if (std.mem.indexOf(u8, sbody, tsym) == null) {
                    try outer_w.print("    _ = {s};\n", .{tsym});
                }
            }
            for (inst.hkt_params) |hp| {
                const hsym = std.fmt.allocPrint(self.alloc, "__F_{s}", .{hp}) catch continue;
                if (std.mem.indexOf(u8, sbody, hsym) == null) {
                    try outer_w.print("    _ = {s};\n", .{hsym});
                }
            }
            for (0..inst.constraints.len) |ci| {
                const wsym = std.fmt.allocPrint(self.alloc, "__W_{d}", .{ci}) catch continue;
                if (std.mem.indexOf(u8, sbody, wsym) == null) {
                    try outer_w.print("    _ = {s};\n", .{wsym});
                }
            }
            try outer_w.writeAll(sbody);
            try outer_w.writeAll("    };\n}\n");
        } else {
            self.indent -= 1;
            try self.w.writeAll("};\n");
        }
    }

    fn emitFnDecl(self: *Emitter, decl: *const ast.Decl) Io.Writer.Error!void {
        const fd = decl.kind.fn_decl;
        const fname = self.checked.declCanonicalName(decl.span.start) orelse self.sourceOf(fd.name);
        const cf = self.findCheckedFn(fname);
        const is_main = std.mem.eql(u8, fname, "main");
        const ret_ty: ?*const sema.Ty = if (cf) |f| f.ret_type else null;

        try self.w.writeAll("fn ");
        if (is_main) {
            try self.w.writeAll("aethel_main");
        } else {
            try self.emitIdent(fname);
        }
        try self.w.writeByte('(');
        var need_comma = false;
        if (cf) |f| {
            for (f.type_params) |tp| {
                if (need_comma) try self.w.writeAll(", ");
                need_comma = true;
                try self.w.print("comptime __T_{s}: type", .{tp});
            }
            for (f.hkt_params) |hp| {
                if (need_comma) try self.w.writeAll(", ");
                need_comma = true;
                try self.w.print("comptime __F_{s}: fn (comptime type) type", .{hp});
            }
            for (0..f.constraint_count) |wi| {
                if (need_comma) try self.w.writeAll(", ");
                need_comma = true;
                try self.w.print("comptime __W_{d}: type", .{wi});
            }
        }
        var mut_slice_count: usize = 0;
        var has_fn_param = false;
        var has_owned_param = false;
        for (fd.params, 0..) |_, pi| {
            const pty: ?*const sema.Ty = if (cf != null and pi < cf.?.param_types.len) cf.?.param_types[pi] else null;
            if (pty) |t| {
                if (t.* == .fn_ty) has_fn_param = true;
                if (isOwnedDynamicTy(t)) has_owned_param = true;
                if (t.* == .slice and t.slice.mutable) {
                    mut_slice_count += 1;
                } else if (t.* == .view and t.view.target.* == .slice and t.view.mode == .exclusive and t.view.target.slice.mutable) {
                    mut_slice_count += 1;
                }
            }
        }
        const wrap_noalias = !is_main and mut_slice_count >= 1 and !has_fn_param and !has_owned_param and
            (cf == null or (cf.?.type_params.len == 0 and cf.?.hkt_params.len == 0 and cf.?.constraint_count == 0));

        var fn_sig_rest: Io.Writer.Allocating = .init(self.alloc);
        const fn_outer_w = self.w;
        self.w = &fn_sig_rest.writer;
        for (fd.params, 0..) |p, pi| {
            if (need_comma) try self.w.writeAll(", ");
            need_comma = true;
            const pty: ?*const sema.Ty = if (cf != null and pi < cf.?.param_types.len) cf.?.param_types[pi] else null;
            const pname = self.sourceOf(p.name);
            const is_owned = isOwnedDynamicTy(pty);
            const has_mv = is_owned and self.stmtsMayMoveIdent(fd.body.stmts, fd.body.tail, pname);
            const is_mut_by_val = (p.mutable or has_mv) and !(pty != null and isPointerType(pty.?));
            if (wrap_noalias) {
                try self.w.print("__na_in_{d}", .{pi});
            } else if (is_mut_by_val) {
                try self.w.print("__param_{s}", .{pname});
            } else {
                try self.emitIdent(pname);
            }
            try self.w.writeAll(": ");
            if (pty != null and pty.?.* == .fn_ty) {
                try self.w.writeAll("anytype");
            } else if (pty) |t| {
                try self.emitTy(t);
            } else if (p.ty) |pt| {
                try self.emitAstType(pt);
            } else {
                try self.w.writeAll("usize");
            }
        }
        try self.w.writeAll(") ");
        if (ret_ty) |rt| {
            try self.emitTy(rt);
        } else if (fd.ret) |rt| {
            try self.emitAstType(rt);
        } else {
            try self.w.writeAll("void");
        }
        try self.w.writeAll(" {\n");

        self.indent += 1;
        const prev_ret = self.current_fn_ret;
        self.current_fn_ret = ret_ty;
        defer self.current_fn_ret = prev_ret;
        const sv_mark = self.pushScopeVars();
        defer self.popScopeVars(sv_mark);

        var fn_body_buf: Io.Writer.Allocating = .init(self.alloc);
        self.w = &fn_body_buf.writer;
        // Bind mutable by-value params to local `var` and silence genuinely unused parameter warnings.
        for (fd.params, 0..) |p, pi| {
            const pty: ?*const sema.Ty = if (cf != null and pi < cf.?.param_types.len) cf.?.param_types[pi] else null;
            const pname = self.sourceOf(p.name);
            const is_owned = isOwnedDynamicTy(pty);
            const has_mv = is_owned and self.stmtsMayMoveIdent(fd.body.stmts, fd.body.tail, pname);
            const is_mut_by_val = (p.mutable or has_mv) and !(pty != null and isPointerType(pty.?));
            const is_var_or_ptr = is_mut_by_val or (pty != null and isPointerType(pty.?));
            if (is_owned) {
                self.bindOwnedScopeVar(pname, pty, is_var_or_ptr, has_mv);
            } else {
                self.bindScopeVar(pname, pty, is_var_or_ptr);
            }
            if (is_mut_by_val) {
                try self.writeIndent();
                try self.w.writeAll("var ");
                try self.emitIdent(pname);
                if (pty != null and pty.?.* != .fn_ty) {
                    try self.w.writeAll(": ");
                    try self.emitTy(pty.?);
                } else if (pty == null) {
                    try self.w.writeAll(": usize");
                }
                try self.w.print(" = __param_{s};\n", .{pname});
                if (!has_mv and !self.blockMutatesOrBorrowsIdent(&fd.body, pname)) {
                    try self.writeIndent();
                    try self.w.writeAll("_ = &");
                    try self.emitIdent(pname);
                    try self.w.writeAll(";\n");
                }
            } else if (!is_owned and !self.blockMentionsIdent(&fd.body, pname)) {
                try self.writeIndent();
                try self.w.writeAll("_ = ");
                try self.emitIdent(pname);
                try self.w.writeAll(";\n");
            }
            if (is_owned) {
                try self.writeIndent();
                try self.w.writeAll("defer ");
                try self.emitIdent(pname);
                try self.w.writeAll(".deinit();\n");
            }
        }

        try self.emitStmtsWithRest(fd.body.stmts, fd.body.tail);
        if (fd.body.tail) |tail| {
            const ret_is_void = if (ret_ty) |rt| isVoidTy(rt) else (fd.ret == null);
            if (ret_is_void) {
                try self.emitTailStmt(tail);
            } else {
                try self.writeIndent();
                try self.w.writeAll("return ");
                if (ret_ty) |rt| {
                    try self.emitCoercedExpr(tail, rt);
                } else {
                    try self.emitExpr(tail);
                }
                try self.w.writeAll(";\n");
            }
        }
        self.indent -= 1;
        try self.w.writeAll("}\n");

        self.w = fn_outer_w;
        try fn_outer_w.writeAll(fn_sig_rest.written());

        if (wrap_noalias) {
            const ret_is_void = if (ret_ty) |rt| isVoidTy(rt) else (fd.ret == null);
            try fn_outer_w.writeAll(if (ret_is_void) "    @call(.always_inline, (struct {\n        fn __noalias_body(" else "    return @call(.always_inline, (struct {\n        fn __noalias_body(");
            for (fd.params, 0..) |p, pi| {
                if (pi > 0) try fn_outer_w.writeAll(", ");
                const pty: ?*const sema.Ty = if (cf != null and pi < cf.?.param_types.len) cf.?.param_types[pi] else null;
                const pname = self.sourceOf(p.name);
                if (pty != null and (pty.?.* == .slice or (pty.?.* == .view and pty.?.view.target.* == .slice))) {
                    const mutable = if (pty.?.* == .slice) pty.?.slice.mutable else (pty.?.view.mode == .exclusive and pty.?.view.target.slice.mutable);
                    const elem = if (pty.?.* == .slice) pty.?.slice.elem else pty.?.view.target.slice.elem;
                    try fn_outer_w.print("noalias __na_{d}_ptr: [*]", .{pi});
                    if (!mutable) try fn_outer_w.writeAll("const ");
                    var el_buf: Io.Writer.Allocating = .init(self.alloc);
                    const saved_w = self.w;
                    self.w = &el_buf.writer;
                    try self.emitTy(elem);
                    self.w = saved_w;
                    try fn_outer_w.writeAll(el_buf.written());
                    try fn_outer_w.print(", __na_{d}_len: usize", .{pi});
                } else {
                    const prev_w = self.w;
                    var na_pbuf: Io.Writer.Allocating = .init(self.alloc);
                    self.w = &na_pbuf.writer;
                    try self.emitIdent(pname);
                    self.w = prev_w;
                    const p_id = na_pbuf.written();
                    const is_owned = isOwnedDynamicTy(pty);
                    const has_mv = is_owned and self.stmtsMayMoveIdent(fd.body.stmts, fd.body.tail, pname);
                    const is_mut_by_val = (p.mutable or has_mv) and !(pty != null and isPointerType(pty.?));
                    if (is_mut_by_val) {
                        try fn_outer_w.print("__param_{s}: ", .{pname});
                    } else {
                        try fn_outer_w.print("{s}: ", .{p_id});
                    }
                    var ty_buf: Io.Writer.Allocating = .init(self.alloc);
                    self.w = &ty_buf.writer;
                    if (pty) |t| {
                        try self.emitTy(t);
                    } else if (p.ty) |pt| {
                        try self.emitAstType(pt);
                    } else {
                        try self.w.writeAll("usize");
                    }
                    self.w = prev_w;
                    try fn_outer_w.writeAll(ty_buf.written());
                }
            }
            try fn_outer_w.writeAll(") ");
            {
                const prev_w = self.w;
                var rt_buf: Io.Writer.Allocating = .init(self.alloc);
                self.w = &rt_buf.writer;
                if (ret_ty) |rt| {
                    try self.emitTy(rt);
                } else if (fd.ret) |rt| {
                    try self.emitAstType(rt);
                } else {
                    try self.w.writeAll("void");
                }
                self.w = prev_w;
                try fn_outer_w.writeAll(rt_buf.written());
            }
            try fn_outer_w.writeAll(" {\n");
            for (fd.params, 0..) |p, pi| {
                const pty: ?*const sema.Ty = if (cf != null and pi < cf.?.param_types.len) cf.?.param_types[pi] else null;
                if (pty != null and (pty.?.* == .slice or (pty.?.* == .view and pty.?.view.target.* == .slice))) {
                    const pname = self.sourceOf(p.name);
                    const prev_w = self.w;
                    var sl_id_buf: Io.Writer.Allocating = .init(self.alloc);
                    self.w = &sl_id_buf.writer;
                    try self.emitIdent(pname);
                    try self.w.writeAll(": ");
                    try self.emitTy(pty.?);
                    self.w = prev_w;
                    if (p.mutable) {
                        try fn_outer_w.print("            const __param_{s} = __na_{d}_ptr[0..__na_{d}_len];\n", .{ pname, pi, pi });
                    } else {
                        try fn_outer_w.print("            const {s} = __na_{d}_ptr[0..__na_{d}_len];\n", .{ sl_id_buf.written(), pi, pi });
                    }
                }
            }
            try fn_outer_w.writeAll(fn_body_buf.written());
            try fn_outer_w.writeAll("    }).__noalias_body, .{ ");
            var need_ca = false;
            for (fd.params, 0..) |_, pi| {
                const pty: ?*const sema.Ty = if (cf != null and pi < cf.?.param_types.len) cf.?.param_types[pi] else null;
                if (need_ca) try fn_outer_w.writeAll(", ");
                need_ca = true;
                if (pty != null and (pty.?.* == .slice or (pty.?.* == .view and pty.?.view.target.* == .slice))) {
                    try fn_outer_w.print("__na_in_{d}.ptr, __na_in_{d}.len", .{ pi, pi });
                } else {
                    try fn_outer_w.print("__na_in_{d}", .{pi});
                }
            }
            try fn_outer_w.writeAll(" });\n}\n");
        } else {
            if (cf) |f| {
                for (f.type_params) |tp| {
                    const tsym = std.fmt.allocPrint(self.alloc, "__T_{s}", .{tp}) catch continue;
                    if (std.mem.indexOf(u8, fn_sig_rest.written(), tsym) == null and
                        std.mem.indexOf(u8, fn_body_buf.written(), tsym) == null)
                    {
                        try fn_outer_w.print("    _ = {s};\n", .{tsym});
                    }
                }
                for (f.hkt_params) |hp| {
                    const hsym = std.fmt.allocPrint(self.alloc, "__F_{s}", .{hp}) catch continue;
                    if (std.mem.indexOf(u8, fn_sig_rest.written(), hsym) == null and
                        std.mem.indexOf(u8, fn_body_buf.written(), hsym) == null)
                    {
                        try fn_outer_w.print("    _ = {s};\n", .{hsym});
                    }
                }
                for (0..f.constraint_count) |wi| {
                    const wsym = std.fmt.allocPrint(self.alloc, "__W_{d}", .{wi}) catch continue;
                    if (std.mem.indexOf(u8, fn_sig_rest.written(), wsym) == null and
                        std.mem.indexOf(u8, fn_body_buf.written(), wsym) == null)
                    {
                        try fn_outer_w.print("    _ = {s};\n", .{wsym});
                    }
                }
            }
            try fn_outer_w.writeAll(fn_body_buf.written());
        }

        if (is_main) {
            try self.w.writeByte('\n');
            try self.w.writeAll("pub fn main(init: std.process.Init) void {\n");
            try self.w.writeAll("    aethel_io = init.io;\n");
            try self.w.writeAll("    aethel_raw_arena = init.arena.allocator();\n");
            try self.w.writeAll("    if (@import(\"builtin\").mode == .debug) { aethel_gpa = init.gpa; }\n");
            if (ret_ty != null and ret_ty.?.isInteger() != null) {
                try self.w.writeAll("    const status = aethel_main();\n");
                try self.w.writeAll("    if (status != 0) std.process.exit(@intCast(status));\n");
            } else if (ret_ty != null and !isVoidTy(ret_ty.?)) {
                try self.w.writeAll("    _ = aethel_main();\n");
            } else {
                try self.w.writeAll("    aethel_main();\n");
            }
            try self.w.writeAll("}\n");
        }
    }

    fn isVoidTy(ty: *const sema.Ty) bool {
        return switch (ty.*) {
            .unit, .err => true,
            .tuple => |elems| elems.len == 0,
            else => false,
        };
    }

    fn isVoidExpr(self: *const Emitter, expr: *const ast.Expr) bool {
        if (self.checked.exprType(expr)) |ty| {
            if (isVoidTy(ty)) return true;
            return false;
        }
        return switch (expr.*) {
            .fork_expr => true,
            .block => |b| if (b.tail) |t| self.isVoidExpr(t) else true,
            else => false,
        };
    }

    fn emitStmtsWithRest(self: *Emitter, stmts: []const ast.Stmt, tail: ?*const ast.Expr) Io.Writer.Error!void {
        for (stmts, 0..) |*st, idx| {
            try self.emitStmt(st, stmts[idx + 1 ..], tail);
        }
    }

    fn emitStmt(
        self: *Emitter,
        stmt: *const ast.Stmt,
        rest_stmts: []const ast.Stmt,
        rest_tail: ?*const ast.Expr,
    ) Io.Writer.Error!void {
        switch (stmt.*) {
            .let_stmt => |ls| {
                const lty = self.checked.letType(ls.span.start);
                switch (ls.pattern.*) {
                    .ident => |id| {
                        const vname = self.sourceOf(id.name);
                        const is_mut = ls.mutable or id.mutable;
                        if (ls.value.* == .list and lty != null and
                            (lty.?.* == .collection or (lty.?.* == .slice and lty.?.slice.mutable)))
                        {
                            const arr_id = self.nextLabel();
                            const elem_ty = if (lty.?.* == .collection) lty.?.collection.elem_ty else lty.?.slice.elem;
                            if (self.tyBackingKind(lty.?)) |bk| {
                                const rec = &self.checked.records[bk.ridx];
                                const n_elems = ls.value.list.elems.len;
                                try self.writeIndent();
                                try self.w.print("const __init_{d} = [_]", .{arr_id});
                                try self.emitTy(elem_ty);
                                try self.w.writeAll("{ ");
                                for (ls.value.list.elems, 0..) |el, ei| {
                                    if (ei > 0) try self.w.writeAll(", ");
                                    try self.emitCoercedExpr(el, elem_ty);
                                }
                                try self.w.writeAll(" };\n");
                                switch (bk.kind) {
                                    .soa => {
                                        for (rec.fields) |f| {
                                            try self.writeIndent();
                                            if (n_elems == 0) {
                                                try self.w.print("var __col_{d}_{s} = [0]", .{ arr_id, f.name });
                                                try self.emitTy(f.ty);
                                                try self.w.writeAll("{};\n");
                                            } else {
                                                try self.w.print("var __col_{d}_{s}: [{d}]", .{ arr_id, f.name, n_elems });
                                                try self.emitTy(f.ty);
                                                try self.w.print(" align(64) = blk_{d}_{s}: {{\n", .{ arr_id, f.name });
                                                try self.writeIndent();
                                                try self.w.print("    var __ca: [{d}]", .{n_elems});
                                                try self.emitTy(f.ty);
                                                try self.w.writeAll(" align(64) = undefined;\n");
                                                try self.writeIndent();
                                                try self.w.print("    for (0..{d}) |__k| __ca[__k] = __init_{d}[__k].", .{ n_elems, arr_id });
                                                try self.emitIdent(f.name);
                                                try self.w.writeAll(";\n");
                                                try self.writeIndent();
                                                try self.w.print("    break :blk_{d}_{s} __ca;\n", .{ arr_id, f.name });
                                                try self.writeIndent();
                                                try self.w.writeAll("};\n");
                                            }
                                        }
                                        try self.writeIndent();
                                        try self.w.writeAll("const ");
                                        try self.emitIdent(vname);
                                        try self.w.writeAll(": ");
                                        try self.emitTy(lty.?);
                                        try self.w.print(" = .{{ .len = {d}", .{n_elems});
                                        for (rec.fields) |f| {
                                            try self.w.writeAll(", .");
                                            try self.emitIdent(f.name);
                                            try self.w.print(" = __col_{d}_{s}[0..]", .{ arr_id, f.name });
                                        }
                                        try self.w.writeAll(" };\n");
                                    },
                                    .aosoa => |w| {
                                        const n_tiles = @max(@as(usize, 1), (n_elems + w - 1) / w);
                                        try self.writeIndent();
                                        try self.w.print("var __tiles_{d}: [{d}]__AethelTile_{d}_{s} align(64) = blk_{d}: {{\n", .{ arr_id, n_tiles, w, rec.name, arr_id });
                                        try self.writeIndent();
                                        try self.w.print("    var __ts: [{d}]__AethelTile_{d}_{s} align(64) = undefined;\n", .{ n_tiles, w, rec.name });
                                        if (n_elems > 0) {
                                            try self.writeIndent();
                                            try self.w.print("    for (0..{d}) |__k| {{\n", .{n_elems});
                                            for (rec.fields) |f| {
                                                try self.writeIndent();
                                                try self.w.print("        __ts[__k / {d}].", .{w});
                                                try self.emitIdent(f.name);
                                                try self.w.print("[__k % {d}] = __init_{d}[__k].", .{ w, arr_id });
                                                try self.emitIdent(f.name);
                                                try self.w.writeAll(";\n");
                                            }
                                            try self.writeIndent();
                                            try self.w.writeAll("    }\n");
                                        }
                                        try self.writeIndent();
                                        try self.w.print("    break :blk_{d} __ts;\n", .{arr_id});
                                        try self.writeIndent();
                                        try self.w.writeAll("};\n");
                                        try self.writeIndent();
                                        try self.w.writeAll("const ");
                                        try self.emitIdent(vname);
                                        try self.w.writeAll(": ");
                                        try self.emitTy(lty.?);
                                        try self.w.print(" = .{{ .tiles = __tiles_{d}[0..], .base_elem = 0, .len = {d} }};\n", .{ arr_id, n_elems });
                                    },
                                    .aos_slice => unreachable,
                                }
                                self.bindScopeVar(vname, lty, false);
                                if (!self.stmtsMentionIdent(rest_stmts, rest_tail, vname)) {
                                    try self.writeIndent();
                                    try self.w.writeAll("_ = ");
                                    try self.emitIdent(vname);
                                    try self.w.writeAll(";\n");
                                }
                                return;
                            }
                            const needs_cache_align = blk: {
                                if (lty.?.* == .collection) {
                                    if (lty.?.collection.elem_record) |ri| {
                                        if (ri < self.checked.records.len) {
                                            if (self.checked.records[ri].collection_layout) |cl| {
                                                break :blk cl == .aosoa or cl == .soa;
                                            }
                                        }
                                    }
                                }
                                break :blk false;
                            };
                            try self.writeIndent();
                            if (needs_cache_align) {
                                try self.w.print("var __arr_{d} align(64) = [_]", .{arr_id});
                            } else {
                                try self.w.print("var __arr_{d} = [_]", .{arr_id});
                            }
                            try self.emitTy(elem_ty);
                            try self.w.writeAll("{ ");
                            for (ls.value.list.elems, 0..) |el, ei| {
                                if (ei > 0) try self.w.writeAll(", ");
                                try self.emitCoercedExpr(el, elem_ty);
                            }
                            try self.w.writeAll(" };\n");
                            try self.writeIndent();
                            try self.w.writeAll("const ");
                            try self.emitIdent(vname);
                            try self.w.writeAll(": ");
                            try self.emitTy(lty.?);
                            try self.w.print(" = __arr_{d}[0..];\n", .{arr_id});
                            self.bindScopeVar(vname, lty, false);
                            if (!self.stmtsMentionIdent(rest_stmts, rest_tail, vname)) {
                                try self.writeIndent();
                                try self.w.writeAll("_ = ");
                                try self.emitIdent(vname);
                                try self.w.writeAll(";\n");
                            }
                            return;
                        }
                        const eff_ty = lty orelse self.checked.exprType(ls.value);
                        const is_owned = isOwnedDynamicTy(eff_ty);
                        const has_mv = is_owned and self.stmtsMayMoveIdent(rest_stmts, rest_tail, vname);
                        const emit_var = is_mut or has_mv;
                        try self.writeIndent();
                        try self.w.writeAll(if (emit_var) "var " else "const ");
                        try self.emitIdent(vname);
                        if (eff_ty) |ty| {
                            if (ty.* != .err and ty.* != .fn_ty) {
                                try self.w.writeAll(": ");
                                try self.emitTy(ty);
                            }
                        }
                        try self.w.writeAll(" = ");
                        if (eff_ty) |ty| {
                            try self.emitCoercedExpr(ls.value, ty);
                        } else {
                            try self.emitExpr(ls.value);
                        }
                        try self.w.writeAll(";\n");
                        if (is_owned) {
                            self.bindOwnedScopeVar(vname, eff_ty, emit_var, has_mv);
                            try self.writeIndent();
                            try self.w.writeAll("defer ");
                            try self.emitIdent(vname);
                            try self.w.writeAll(".deinit();\n");
                            if (emit_var and !has_mv and !self.stmtsMutateOrBorrowIdent(rest_stmts, rest_tail, vname)) {
                                try self.writeIndent();
                                try self.w.writeAll("_ = &");
                                try self.emitIdent(vname);
                                try self.w.writeAll(";\n");
                            }
                        } else {
                            self.bindScopeVar(vname, eff_ty, is_mut);
                            if (is_mut) {
                                if (!self.stmtsMutateOrBorrowIdent(rest_stmts, rest_tail, vname)) {
                                    try self.writeIndent();
                                    try self.w.writeAll("_ = &");
                                    try self.emitIdent(vname);
                                    try self.w.writeAll(";\n");
                                }
                            } else if (!self.stmtsMentionIdent(rest_stmts, rest_tail, vname)) {
                                try self.writeIndent();
                                try self.w.writeAll("_ = ");
                                try self.emitIdent(vname);
                                try self.w.writeAll(";\n");
                            }
                        }
                    },
                    .wildcard => {
                        try self.writeIndent();
                        if (isOwnedDynamicTy(self.checked.exprType(ls.value))) {
                            const dlbl = self.nextLabel();
                            try self.w.print("{{ const __drop_{d} = ", .{dlbl});
                            try self.emitExpr(ls.value);
                            try self.w.print("; __drop_{d}.deinit(); }}\n", .{dlbl});
                        } else if (self.isVoidExpr(ls.value)) {
                            try self.emitExpr(ls.value);
                            try self.w.writeAll(";\n");
                        } else {
                            try self.w.writeAll("_ = ");
                            try self.emitExpr(ls.value);
                            try self.w.writeAll(";\n");
                        }
                    },
                    .tuple => |tp| {
                        const tmp_id = self.nextLabel();
                        try self.writeIndent();
                        try self.w.print("const __tup_{d} = ", .{tmp_id});
                        try self.emitExpr(ls.value);
                        try self.w.writeAll(";\n");
                        for (tp.elems, 0..) |el, ei| {
                            if (el.* == .ident) {
                                const en = self.sourceOf(el.ident.name);
                                const is_el_mut = ls.mutable or el.ident.mutable;
                                try self.writeIndent();
                                try self.w.writeAll(if (is_el_mut) "var " else "const ");
                                try self.emitIdent(en);
                                try self.w.print(" = __tup_{d}[{d}];\n", .{ tmp_id, ei });
                                if (is_el_mut) {
                                    if (!self.stmtsMutateOrBorrowIdent(rest_stmts, rest_tail, en)) {
                                        try self.writeIndent();
                                        try self.w.writeAll("_ = &");
                                        try self.emitIdent(en);
                                        try self.w.writeAll(";\n");
                                    }
                                } else if (!self.stmtsMentionIdent(rest_stmts, rest_tail, en)) {
                                    try self.writeIndent();
                                    try self.w.writeAll("_ = ");
                                    try self.emitIdent(en);
                                    try self.w.writeAll(";\n");
                                }
                            }
                        }
                    },
                    else => {
                        try self.writeIndent();
                        try self.w.writeAll("_ = ");
                        try self.emitExpr(ls.value);
                        try self.w.writeAll(";\n");
                    },
                }
            },
            .use_stmt => |us| {
                const tmp_id = self.nextLabel();
                try self.writeIndent();
                try self.w.print("const __use_{d} = ", .{tmp_id});
                try self.emitExpr(us.expr);
                try self.w.writeAll(";\n");
                if (us.patterns.len > 0 and us.patterns[0].* == .ident) {
                    const bn = self.sourceOf(us.patterns[0].ident.name);
                    try self.writeIndent();
                    try self.w.writeAll("const ");
                    try self.emitIdent(bn);
                    try self.w.print(" = __use_{d};\n", .{tmp_id});
                    self.bindScopeVar(bn, self.checked.exprType(us.expr), false);
                    if (!self.stmtsMentionIdent(rest_stmts, rest_tail, bn)) {
                        try self.writeIndent();
                        try self.w.writeAll("_ = ");
                        try self.emitIdent(bn);
                        try self.w.writeAll(";\n");
                    }
                } else {
                    try self.writeIndent();
                    try self.w.print("_ = __use_{d};\n", .{tmp_id});
                }
            },
            .assign_stmt => |asg| {
                const target_ty = self.checked.exprType(asg.target) orelse if (asg.target.* == .ident) blk: {
                    if (self.lookupScopeVar(self.sourceOf(asg.target.ident))) |sv| break :blk sv.ty;
                    break :blk null;
                } else null;
                if (asg.target.* == .field and asg.target.field.target.* == .index) {
                    const ix = asg.target.field.target.index;
                    const ix_tty = self.checked.exprType(ix.target);
                    const is_vec_tgt = self.isVecTyOrViewToVec(ix_tty);
                    if (self.tyBackingKind(ix_tty)) |bk| {
                        const fname = self.sourceOf(asg.target.field.name);
                        switch (bk.kind) {
                            .soa => {
                                try self.writeIndent();
                                if (is_vec_tgt) {
                                    try self.w.writeByte('(');
                                    try self.emitExpr(ix.target);
                                    try self.w.writeAll(").mutView().");
                                } else {
                                    try self.emitExpr(ix.target);
                                    try self.w.writeByte('.');
                                }
                                try self.emitIdent(fname);
                                try self.w.writeByte('[');
                                try self.emitSliceIndexExpr(ix.idx);
                                try self.w.print("] {s} ", .{asg.op.symbol()});
                                try self.emitAssignmentOperand(asg.value, asg.op, target_ty);
                                try self.w.writeAll(";\n");
                                return;
                            },
                            .aosoa => |w| {
                                const albl = self.nextLabel();
                                try self.writeIndent();
                                if (is_vec_tgt) {
                                    try self.w.print("{{ const __ac_{d} = (", .{albl});
                                    try self.emitExpr(ix.target);
                                    try self.w.print(").mutView(); const __aa_{d} = __ac_{d}.base_elem + ", .{ albl, albl });
                                } else {
                                    try self.w.print("{{ const __ac_{d} = &", .{albl});
                                    try self.emitExpr(ix.target);
                                    try self.w.print("; const __aa_{d} = __ac_{d}.base_elem + ", .{ albl, albl });
                                }
                                try self.emitSliceIndexExpr(ix.idx);
                                try self.w.print("; __ac_{d}.tiles[__aa_{d} / {d}].", .{ albl, albl, w });
                                try self.emitIdent(fname);
                                try self.w.print("[__aa_{d} % {d}] {s} ", .{ albl, w, asg.op.symbol() });
                                try self.emitAssignmentOperand(asg.value, asg.op, target_ty);
                                try self.w.writeAll("; }\n");
                                return;
                            },
                            .aos_slice => {},
                        }
                    } else if (is_vec_tgt) {
                        const fname = self.sourceOf(asg.target.field.name);
                        try self.writeIndent();
                        try self.w.writeByte('(');
                        try self.emitExpr(ix.target);
                        try self.w.writeAll(").mutSlice()[");
                        try self.emitSliceIndexExpr(ix.idx);
                        try self.w.writeAll("].");
                        try self.emitIdent(fname);
                        try self.w.print(" {s} ", .{asg.op.symbol()});
                        try self.emitAssignmentOperand(asg.value, asg.op, target_ty);
                        try self.w.writeAll(";\n");
                        return;
                    }
                }
                if (asg.target.* == .index) {
                    const ix = asg.target.index;
                    const ix_tty = self.checked.exprType(ix.target);
                    const has_bk = self.tyBackingKind(ix_tty) != null;
                    const is_vec_tgt = self.isVecTyOrViewToVec(ix_tty);
                    if (has_bk and asg.op == .assign) {
                        try self.writeIndent();
                        if (is_vec_tgt) try self.w.writeAll("_ = ");
                        try self.emitExpr(ix.target);
                        try self.w.writeAll(if (is_vec_tgt) ".setChecked(@intCast(" else ".set(");
                        try self.emitSliceIndexExpr(ix.idx);
                        try self.w.writeAll(if (is_vec_tgt) "), " else ", ");
                        try self.emitAssignmentOperand(asg.value, asg.op, target_ty);
                        try self.w.writeAll(");\n");
                        return;
                    } else if (!has_bk and is_vec_tgt) {
                        try self.writeIndent();
                        try self.w.writeByte('(');
                        try self.emitExpr(ix.target);
                        try self.w.writeAll(").mutSlice()[");
                        try self.emitSliceIndexExpr(ix.idx);
                        try self.w.print("] {s} ", .{asg.op.symbol()});
                        try self.emitAssignmentOperand(asg.value, asg.op, target_ty);
                        try self.w.writeAll(";\n");
                        return;
                    }
                }
                if (asg.target.* == .ident and asg.op == .assign and isOwnedDynamicTy(target_ty)) {
                    const albl = self.nextLabel();
                    try self.writeIndent();
                    try self.w.print("{{ const __rasg_{d} = ", .{albl});
                    try self.emitCoercedExpr(asg.value, target_ty.?);
                    try self.w.writeAll("; ");
                    try self.emitExpr(asg.target);
                    try self.w.writeAll(".deinit(); ");
                    try self.emitExpr(asg.target);
                    try self.w.print(" = __rasg_{d}; }}\n", .{albl});
                    return;
                }
                try self.writeIndent();
                try self.emitExpr(asg.target);
                try self.w.print(" {s} ", .{asg.op.symbol()});
                try self.emitAssignmentOperand(asg.value, asg.op, target_ty);
                try self.w.writeAll(";\n");
            },
            .return_stmt => |rs| {
                try self.writeIndent();
                if (rs.value) |v| {
                    try self.w.writeAll("return ");
                    if (self.current_fn_ret) |rt| {
                        try self.emitCoercedExpr(v, rt);
                    } else {
                        try self.emitExpr(v);
                    }
                    try self.w.writeAll(";\n");
                } else {
                    try self.w.writeAll("return;\n");
                }
            },
            .while_stmt => |ws| {
                try self.writeIndent();
                try self.w.writeAll("while (");
                try self.emitExpr(ws.cond);
                try self.w.writeAll(") {\n");
                self.indent += 1;
                try self.emitStmtsWithRest(ws.body.stmts, ws.body.tail);
                if (ws.body.tail) |t| try self.emitTailStmt(t);
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("}\n");
            },
            .for_stmt => |fs| {
                try self.emitForStmt(&fs);
            },
            .expr_stmt => |es| {
                try self.emitTailStmt(es.expr);
            },
        }
    }

    fn isCollectionMapInPlaceExpr(self: *const Emitter, expr: *const ast.Expr) bool {
        return expr.* == .binary and
            expr.binary.op == .pipe and
            expr.binary.right.* == .call and
            expr.binary.right.call.callee.* == .ident and
            std.mem.eql(u8, self.sourceOf(expr.binary.right.call.callee.ident), "map_in_place");
    }

    fn hasExternMarshaledArg(self: *const Emitter, pt: *const sema.Ty) bool {
        if (pt.* == .string or pt.* == .fn_ty) return true;
        if (pt.* == .slice or (pt.* == .view and pt.view.target.* == .slice)) return true;
        return self.tyBackingKind(pt) != null;
    }

    fn isBlockLikeVoidExpr(self: *const Emitter, expr: *const ast.Expr) bool {
        return switch (expr.*) {
            .if_expr, .block, .view_expr, .fork_expr, .case_expr => true,
            .using_expr => |ue| self.isBlockLikeVoidExpr(ue.target),
            .call => |c| blk: {
                const resolved_name = self.checked.resolvedCallName(c.callee) orelse
                    if (c.callee.* == .ident) self.sourceOf(c.callee.ident) else null;
                if (resolved_name) |rn| {
                    if (self.findCheckedFn(rn)) |cf| {
                        if (cf.has_extern_abi) {
                            for (cf.param_types) |pt| {
                                if (self.hasExternMarshaledArg(pt)) break :blk true;
                            }
                        }
                    }
                }
                break :blk false;
            },
            .binary => |b| b.op == .pipe and b.right.* == .call and blk: {
                if (b.right.call.callee.* == .ident) {
                    const cn = self.sourceOf(b.right.call.callee.ident);
                    if (std.mem.eql(u8, cn, "map_in_place")) break :blk true;
                }
                const resolved_name = self.checked.resolvedCallName(b.right.call.callee) orelse
                    if (b.right.call.callee.* == .ident) self.sourceOf(b.right.call.callee.ident) else null;
                if (resolved_name) |rn| {
                    if (self.findCheckedFn(rn)) |cf| {
                        if (cf.has_extern_abi) {
                            for (cf.param_types) |pt| {
                                if (self.hasExternMarshaledArg(pt)) break :blk true;
                            }
                        }
                    }
                }
                break :blk false;
            },
            else => false,
        };
    }

    fn emitTailStmt(self: *Emitter, expr: *const ast.Expr) Io.Writer.Error!void {
        try self.writeIndent();
        if (self.isCollectionMapInPlaceExpr(expr)) {
            const pipe = self.flattenCollectionPipeline(expr);
            if (pipe.map_stages.len > 0 and pipe.fold_arg == null) {
                try self.emitCollectionPipeline(expr, pipe, false);
                try self.w.writeByte('\n');
                return;
            }
        }
        if (self.isVoidExpr(expr)) {
            try self.emitExpr(expr);
            if (self.isBlockLikeVoidExpr(expr)) {
                try self.w.writeByte('\n');
            } else {
                try self.w.writeAll(";\n");
            }
        } else if (isOwnedDynamicTy(self.checked.exprType(expr))) {
            const dlbl = self.nextLabel();
            try self.w.print("{{ const __drop_{d} = ", .{dlbl});
            try self.emitExpr(expr);
            try self.w.print("; __drop_{d}.deinit(); }}\n", .{dlbl});
        } else {
            try self.w.writeAll("_ = ");
            try self.emitExpr(expr);
            try self.w.writeAll(";\n");
        }
    }

    fn emitForStmt(self: *Emitter, fs: anytype) Io.Writer.Error!void {
        if (fs.iter.* == .binary and (fs.iter.binary.op == .range or fs.iter.binary.op == .range_eq)) {
            const b = fs.iter.binary;
            const inclusive = b.op == .range_eq;
            const idx_id = self.nextLabel();
            const iter_ty = self.checked.exprType(fs.iter);

            try self.writeIndent();
            try self.w.writeAll("{\n");
            self.indent += 1;

            try self.writeIndent();
            try self.w.print("var __i_{d}", .{idx_id});
            if (iter_ty) |it| {
                if (it.* != .err) {
                    try self.w.writeAll(": ");
                    try self.emitTy(it);
                }
            } else {
                try self.w.writeAll(": i64");
            }
            try self.w.writeAll(" = ");
            try self.emitIntegerOperand(b.left, iter_ty);
            try self.w.writeAll(";\n");

            try self.writeIndent();
            try self.w.print("const __end_{d}", .{idx_id});
            if (iter_ty) |it| {
                if (it.* != .err) {
                    try self.w.writeAll(": ");
                    try self.emitTy(it);
                }
            } else {
                try self.w.writeAll(": i64");
            }
            try self.w.writeAll(" = ");
            try self.emitIntegerOperand(b.right, iter_ty);
            try self.w.writeAll(";\n");

            try self.writeIndent();
            if (inclusive) {
                try self.w.print("if (__i_{d} <= __end_{d}) {{\n", .{ idx_id, idx_id });
                self.indent += 1;
                try self.writeIndent();
                try self.w.writeAll("while (true) {\n");
            } else {
                try self.w.print("while (__i_{d} < __end_{d}) : (__i_{d} += 1) {{\n", .{ idx_id, idx_id, idx_id });
            }
            self.indent += 1;

            if (fs.pattern.* == .ident) {
                const pname = self.sourceOf(fs.pattern.ident.name);
                try self.writeIndent();
                try self.w.writeAll("const ");
                try self.emitIdent(pname);
                try self.w.print(" = __i_{d};\n", .{idx_id});
                self.bindScopeVar(pname, iter_ty, false);
                if (!self.blockMentionsIdent(&fs.body, pname)) {
                    try self.writeIndent();
                    try self.w.writeAll("_ = ");
                    try self.emitIdent(pname);
                    try self.w.writeAll(";\n");
                }
            }
            const fsv_mark = self.pushScopeVars();
            defer self.popScopeVars(fsv_mark);
            try self.emitStmtsWithRest(fs.body.stmts, fs.body.tail);
            if (fs.body.tail) |t| try self.emitTailStmt(t);

            if (inclusive) {
                try self.writeIndent();
                try self.w.print("if (__i_{d} == __end_{d}) break;\n", .{ idx_id, idx_id });
                try self.writeIndent();
                try self.w.print("__i_{d} += 1;\n", .{idx_id});
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("}\n");
            }
            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeAll("}\n");

            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeAll("}\n");
            return;
        }

        // Collection / slice / Vec iteration
        const iter_ty = self.checked.exprType(fs.iter);
        const iter_bk = self.tyBackingKind(iter_ty);
        const iter_is_vec = self.isVecTyOrViewToVec(iter_ty);
        if (iter_bk != null) {
            const flbl = self.nextLabel();
            try self.writeIndent();
            try self.w.print("const __fiter_{d} = ", .{flbl});
            if (iter_is_vec) {
                try self.w.writeByte('(');
                try self.emitExpr(fs.iter);
                try self.w.writeAll(").asView()");
            } else {
                try self.emitExpr(fs.iter);
            }
            try self.w.writeAll(";\n");
            try self.writeIndent();
            try self.w.print("for (0..__fiter_{d}.len) |__fk_{d}| {{\n", .{ flbl, flbl });
            self.indent += 1;
            const fsv_mark = self.pushScopeVars();
            defer self.popScopeVars(fsv_mark);
            switch (fs.pattern.*) {
                .ident => |id| {
                    const pn = self.sourceOf(id.name);
                    try self.writeIndent();
                    try self.w.writeAll("const ");
                    try self.emitIdent(pn);
                    try self.w.print(" = __fiter_{d}.get(__fk_{d});\n", .{ flbl, flbl });
                    const it_inner: ?*const sema.Ty = if (iter_ty) |t| switch (t.*) {
                        .view => |v| v.target,
                        .path_borrow => |pb| pb.base,
                        else => t,
                    } else null;
                    const el_ty: ?*const sema.Ty = if (it_inner) |t| switch (t.*) {
                        .collection => |c| c.elem_ty,
                        .vec => |v| v.elem_ty,
                        else => null,
                    } else null;
                    self.bindScopeVar(pn, el_ty, false);
                    if (!self.blockMentionsIdent(&fs.body, pn)) {
                        try self.writeIndent();
                        try self.w.writeAll("_ = ");
                        try self.emitIdent(pn);
                        try self.w.writeAll(";\n");
                    }
                },
                else => {},
            }
            try self.emitStmtsWithRest(fs.body.stmts, fs.body.tail);
            if (fs.body.tail) |t| try self.emitTailStmt(t);
            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeAll("}\n");
            return;
        }
        try self.writeIndent();
        try self.w.writeAll("for (");
        if (iter_is_vec) {
            try self.w.writeByte('(');
            try self.emitExpr(fs.iter);
            try self.w.writeAll(").asSlice()");
        } else {
            try self.emitExpr(fs.iter);
        }
        try self.w.writeAll(") |");
        const csv_mark = self.pushScopeVars();
        defer self.popScopeVars(csv_mark);
        switch (fs.pattern.*) {
            .ident => |id| {
                const pn = self.sourceOf(id.name);
                try self.emitIdent(pn);
                try self.w.writeAll("| {\n");
                self.indent += 1;
                const it_inner: ?*const sema.Ty = if (iter_ty) |t| switch (t.*) {
                    .view => |v| v.target,
                    .path_borrow => |pb| pb.base,
                    else => t,
                } else null;
                const el_ty: ?*const sema.Ty = if (it_inner) |t| switch (t.*) {
                    .collection => |c| c.elem_ty,
                    .vec => |v| v.elem_ty,
                    .slice => |s| s.elem,
                    else => null,
                } else null;
                self.bindScopeVar(pn, el_ty, false);
                if (!self.blockMentionsIdent(&fs.body, pn)) {
                    try self.writeIndent();
                    try self.w.writeAll("_ = ");
                    try self.emitIdent(pn);
                    try self.w.writeAll(";\n");
                }
            },
            else => {
                try self.w.writeAll("_| {\n");
                self.indent += 1;
            },
        }
        try self.emitStmtsWithRest(fs.body.stmts, fs.body.tail);
        if (fs.body.tail) |t| try self.emitTailStmt(t);
        self.indent -= 1;
        try self.writeIndent();
        try self.w.writeAll("}\n");
    }

    fn isUnsizedIntLit(self: *const Emitter, expr: *const ast.Expr) ?struct { negative: bool, mag: u128 } {
        if (expr.* == .int_lit) {
            const p = int_range.parseIntLiteral(self.sourceOf(expr.int_lit)) orelse return null;
            if (p.suffix != null) return null;
            return .{ .negative = false, .mag = p.value };
        }
        if (expr.* == .unary and expr.unary.op == .neg and expr.unary.operand.* == .int_lit) {
            const p = int_range.parseIntLiteral(self.sourceOf(expr.unary.operand.int_lit)) orelse return null;
            if (p.suffix != null) return null;
            return .{ .negative = true, .mag = p.value };
        }
        return null;
    }

    fn emitVecListLiteral(self: *Emitter, elems: []const *const ast.Expr, vec_ty: *const sema.Ty) Io.Writer.Error!void {
        try self.emitTy(vec_ty);
        if (elems.len == 0) {
            try self.w.writeAll(".new()");
            return;
        }
        const elem_ty = vec_ty.vec.elem_ty;
        try self.w.writeAll(".fromSlice(&[_]");
        try self.emitTy(elem_ty);
        try self.w.writeAll("{ ");
        for (elems, 0..) |el, ei| {
            if (ei > 0) try self.w.writeAll(", ");
            try self.emitCoercedExpr(el, elem_ty);
        }
        try self.w.writeAll(" })");
    }

    fn tryEmitMoveOwnedExpr(self: *Emitter, expr: *const ast.Expr, target: *const sema.Ty) Io.Writer.Error!bool {
        switch (expr.*) {
            .ident => |sp| {
                const vname = self.sourceOf(sp);
                if (self.lookupScopeVar(vname)) |sv| {
                    if (sv.is_owned_dyn and sv.has_moved_flag) {
                        const mlbl = self.nextLabel();
                        try self.w.print("blk_{d}: {{ const __mv_{d} = ", .{ mlbl, mlbl });
                        try self.emitIdent(vname);
                        try self.w.writeAll("; ");
                        try self.emitIdent(vname);
                        try self.w.print(" = .{{}}; break :blk_{d} __mv_{d}; }}", .{ mlbl, mlbl });
                        return true;
                    }
                }
                return false;
            },
            .block => |*blk| {
                if (blk.tail) |t| {
                    if (self.exprIsDirectMoveAnyOwned(t)) {
                        const mlbl = self.nextLabel();
                        try self.w.print("blk_{d}: {{\n", .{mlbl});
                        self.indent += 1;
                        const bsv = self.pushScopeVars();
                        defer self.popScopeVars(bsv);
                        try self.emitStmtsWithRest(blk.stmts, blk.tail);
                        try self.writeIndent();
                        try self.w.print("break :blk_{d} ", .{mlbl});
                        try self.emitCoercedExpr(t, target);
                        try self.w.writeAll(";\n");
                        self.indent -= 1;
                        try self.writeIndent();
                        try self.w.writeByte('}');
                        return true;
                    }
                }
                return false;
            },
            .if_expr => |ie| {
                if (ie.else_branch) |eb| {
                    const tt_moved = if (ie.then_block.tail) |tt| self.exprIsDirectMoveAnyOwned(tt) else false;
                    if (tt_moved or self.exprIsDirectMoveAnyOwned(eb)) {
                        const mlbl = self.nextLabel();
                        try self.w.writeAll("if (");
                        try self.emitExpr(ie.cond);
                        try self.w.print(") blk_{d}: {{\n", .{mlbl});
                        self.indent += 1;
                        const tsv = self.pushScopeVars();
                        try self.emitStmtsWithRest(ie.then_block.stmts, ie.then_block.tail);
                        if (ie.then_block.tail) |tt| {
                            try self.writeIndent();
                            try self.w.print("break :blk_{d} ", .{mlbl});
                            try self.emitCoercedExpr(tt, target);
                            try self.w.writeAll(";\n");
                        }
                        self.popScopeVars(tsv);
                        self.indent -= 1;
                        try self.writeIndent();
                        try self.w.writeAll("} else ");
                        try self.emitCoercedExpr(eb, target);
                        return true;
                    }
                }
                return false;
            },
            else => return false,
        }
    }

    fn emitCoercedExpr(self: *Emitter, expr: *const ast.Expr, target: *const sema.Ty) Io.Writer.Error!void {
        if (target.* == .err) {
            try self.emitExpr(expr);
            return;
        }
        if (target.* == .vec and expr.* == .list) {
            try self.emitVecListLiteral(expr.list.elems, target);
            return;
        }
        if (isOwnedDynamicTy(target)) {
            if (try self.tryEmitMoveOwnedExpr(expr, target)) return;
        }
        const target_inner: *const sema.Ty = switch (target.*) {
            .view => |v| v.target,
            .path_borrow => |pb| pb.base,
            else => target,
        };
        if ((target_inner.* == .collection or target_inner.* == .slice) and
            self.isVecTyOrViewToVec(self.checked.exprType(expr)))
        {
            const use_mut = switch (target.*) {
                .view => |v| v.mode == .exclusive,
                .path_borrow => |pb| pb.mode == null or pb.mode.? == .exclusive,
                .slice => |s| s.mutable,
                .collection => false,
                else => false,
            };
            try self.w.writeByte('(');
            try self.emitExpr(expr);
            if (self.tyBackingKind(target) != null) {
                try self.w.writeAll(if (use_mut) ").mutView()" else ").asView()");
            } else {
                try self.w.writeAll(if (use_mut) ").mutSlice()" else ").asSlice()");
            }
            return;
        }
        if (target.isInteger()) |target_int| {
            if (self.isUnsizedIntLit(expr)) |lit| {
                try self.w.print("@as({c}{d}, ", .{
                    if (target_int.signed) @as(u8, 'i') else @as(u8, 'u'),
                    target_int.bits,
                });
                if (lit.negative and lit.mag != 0) {
                    try self.w.print("-{d}", .{lit.mag});
                } else {
                    try self.w.print("{d}", .{lit.mag});
                }
                try self.w.writeByte(')');
                return;
            }
            if (self.checked.exprType(expr)) |src_ty| {
                if (src_ty.isInteger()) |src_int| {
                    if (src_int.signed == target_int.signed and src_int.bits == target_int.bits) {
                        try self.emitExpr(expr);
                        return;
                    }
                    try self.w.print("@as({c}{d}, @intCast(", .{
                        if (target_int.signed) @as(u8, 'i') else @as(u8, 'u'),
                        target_int.bits,
                    });
                    try self.emitExpr(expr);
                    try self.w.writeAll("))");
                    return;
                }
            }
        }
        if ((target.* == .f32 or target.* == .f64) and expr.* == .float_lit) {
            try self.emitFloatLitWithTarget(expr.float_lit, target.* == .f32);
            return;
        }
        if (target.* == .option and expr.* == .upper_ident and std.mem.eql(u8, self.sourceOf(expr.upper_ident), "None")) {
            try self.w.writeAll("null");
            return;
        }
        if (isPointerType(target)) {
            const src_ty = self.checked.exprType(expr);
            if (src_ty == null or !isPointerType(src_ty.?)) {
                try self.w.writeByte('&');
                try self.emitExpr(expr);
                return;
            }
        }
        try self.emitExpr(expr);
    }

    fn emitFloatLitWithTarget(self: *Emitter, span: ast.Span, is_f32: bool) Io.Writer.Error!void {
        var raw = self.sourceOf(span);
        var f32_explicit = is_f32;
        if (std.mem.endsWith(u8, raw, "_f32")) {
            raw = raw[0 .. raw.len - 4];
            f32_explicit = true;
        } else if (std.mem.endsWith(u8, raw, "f32")) {
            raw = raw[0 .. raw.len - 3];
            f32_explicit = true;
        } else if (std.mem.endsWith(u8, raw, "_f64")) {
            raw = raw[0 .. raw.len - 4];
        } else if (std.mem.endsWith(u8, raw, "f64")) {
            raw = raw[0 .. raw.len - 3];
        }
        try self.w.print("@as({s}, {s})", .{ if (f32_explicit) "f32" else "f64", raw });
    }

    fn emitStringLit(self: *Emitter, span: ast.Span) Io.Writer.Error!void {
        const raw = self.sourceOf(span);
        if (raw.len < 2) {
            try self.w.writeAll("\"\"");
            return;
        }
        try self.w.writeByte('"');
        const inner = raw[1 .. raw.len - 1];
        var i: usize = 0;
        while (i < inner.len) : (i += 1) {
            const c = inner[i];
            if (c == '\\' and i + 1 < inner.len) {
                const next = inner[i + 1];
                if (next == '0') {
                    // Aethel `\0` lowers to Zig `\x00`.
                    try self.w.writeAll("\\x00");
                    i += 1;
                    continue;
                }
                try self.w.writeByte('\\');
                try self.w.writeByte(next);
                i += 1;
                continue;
            }
            switch (c) {
                '\n' => try self.w.writeAll("\\n"),
                '\r' => try self.w.writeAll("\\r"),
                else => try self.w.writeByte(c),
            }
        }
        try self.w.writeByte('"');
    }

    fn commonIntType(a: int_range.IntType, b: int_range.IntType) int_range.IntType {
        if (a.signed == b.signed) {
            return .{ .signed = a.signed, .bits = @max(a.bits, b.bits) };
        }
        const u_bits = if (!a.signed) a.bits else b.bits;
        const s_bits = if (a.signed) a.bits else b.bits;
        const need_u_signed: u16 = @min(@as(u16, 65535), u_bits +| 1);
        return .{ .signed = true, .bits = @max(s_bits, need_u_signed) };
    }

    fn emitExpr(self: *Emitter, expr: *const ast.Expr) Io.Writer.Error!void {
        switch (expr.*) {
            .int_lit => |sp| {
                const ty_opt = self.checked.exprType(expr);
                const parsed = int_range.parseIntLiteral(self.sourceOf(sp)) orelse {
                    try self.w.writeAll(self.sourceOf(sp));
                    return;
                };
                const target_int: ?int_range.IntType = parsed.suffix orelse if (ty_opt) |t| t.isInteger() else null;
                if (target_int) |it| {
                    try self.w.print("@as({c}{d}, {d})", .{
                        if (it.signed) @as(u8, 'i') else @as(u8, 'u'),
                        it.bits,
                        parsed.value,
                    });
                } else {
                    try self.w.print("{d}", .{parsed.value});
                }
            },
            .float_lit => |sp| {
                const ty_opt = self.checked.exprType(expr);
                try self.emitFloatLitWithTarget(sp, ty_opt != null and ty_opt.?.* == .f32);
            },
            .string_lit => |sp| try self.emitStringLit(sp),
            .bool_lit => |bl| try self.w.writeAll(if (bl.value) "true" else "false"),
            .ident => |sp| {
                const name = self.sourceOf(sp);
                if (self.isDerefIdent(name)) {
                    try self.w.writeAll("(__ctx.");
                    try self.emitIdent(name);
                    try self.w.writeAll(".*)");
                } else if (self.isCtxValueIdent(name)) {
                    try self.w.writeAll("__ctx.");
                    try self.emitIdent(name);
                } else if (self.checked.resolvedIdentName(expr)) |rname| {
                    try self.emitIdent(rname);
                } else {
                    try self.emitIdent(name);
                }
            },
            .upper_ident => |sp| {
                const name = self.sourceOf(sp);
                if (std.mem.eql(u8, name, "None")) {
                    try self.w.writeAll("null");
                    return;
                }
                if (self.findCheckedVariant(null, name)) |found| {
                    const adt_def = &self.checked.adts[found.aidx];
                    if (isPureEnumADT(adt_def)) {
                        try self.emitIdent(adt_def.name);
                        try self.w.writeByte('.');
                        try self.emitIdent(name);
                    } else if (isCompactPackedADT(adt_def)) {
                        try self.emitIdent(adt_def.name);
                        try self.w.writeAll("{ .tag = .");
                        try self.emitIdent(name);
                        try self.w.writeAll(", .payload = 0 }");
                    } else {
                        try self.emitIdent(adt_def.name);
                        try self.w.writeAll("{ .");
                        try self.emitIdent(name);
                        try self.w.writeAll(" = {} }");
                    }
                    return;
                }
                try self.emitIdent(name);
            },
            .placeholder => try self.w.writeAll("{}"),
            .unary => |u| {
                if (u.op == .neg and u.operand.* == .int_lit) {
                    const parsed = int_range.parseIntLiteral(self.sourceOf(u.operand.int_lit)) orelse {
                        try self.w.writeAll("-(");
                        try self.emitExpr(u.operand);
                        try self.w.writeByte(')');
                        return;
                    };
                    const ty_opt = self.checked.exprType(expr);
                    const target_int: ?int_range.IntType = parsed.suffix orelse if (ty_opt) |t| t.isInteger() else null;
                    if (target_int) |it| {
                        try self.w.print("@as({c}{d}, -{d})", .{
                            if (it.signed) @as(u8, 'i') else @as(u8, 'u'),
                            it.bits,
                            parsed.value,
                        });
                    } else {
                        try self.w.print("-{d}", .{parsed.value});
                    }
                    return;
                }
                switch (u.op) {
                    .neg => {
                        const ty_opt = self.checked.exprType(expr);
                        try self.w.writeAll("(-(");
                        if (ty_opt) |t| {
                            try self.emitCoercedExpr(u.operand, t);
                        } else {
                            try self.emitExpr(u.operand);
                        }
                        try self.w.writeAll("))");
                    },
                    .not => {
                        try self.w.writeAll("(!(");
                        try self.emitExpr(u.operand);
                        try self.w.writeAll("))");
                    },
                    .bit_not => {
                        try self.w.writeAll("(~(");
                        try self.emitExpr(u.operand);
                        try self.w.writeAll("))");
                    },
                    .move_op => try self.emitExpr(u.operand),
                    .addr_of => {
                        try self.w.writeAll("(&(");
                        try self.emitExpr(u.operand);
                        try self.w.writeAll("))");
                    },
                }
            },
            .binary => |b| try self.emitBinary(expr, &b),
            .cast => |c| {
                const target_ty = self.checked.exprType(expr);
                const inner_ty = self.checked.exprType(c.expr);
                if (target_ty) |tt| {
                    if (tt.isInteger() != null and (inner_ty == null or inner_ty.?.isInteger() != null)) {
                        try self.emitCoercedExpr(c.expr, tt);
                        return;
                    }
                    if ((tt.* == .f32 or tt.* == .f64) and inner_ty != null and inner_ty.?.isInteger() != null) {
                        try self.w.writeAll("@as(");
                        try self.emitTy(tt);
                        try self.w.writeAll(", @floatFromInt(");
                        try self.emitExpr(c.expr);
                        try self.w.writeAll("))");
                        return;
                    }
                    if (tt.isInteger() != null and inner_ty != null and (inner_ty.?.* == .f32 or inner_ty.?.* == .f64)) {
                        try self.w.writeAll("@as(");
                        try self.emitTy(tt);
                        try self.w.writeAll(", @intFromFloat(");
                        try self.emitExpr(c.expr);
                        try self.w.writeAll("))");
                        return;
                    }
                    try self.w.writeAll("@as(");
                    try self.emitTy(tt);
                    try self.w.writeAll(", ");
                    try self.emitExpr(c.expr);
                    try self.w.writeByte(')');
                } else {
                    try self.emitExpr(c.expr);
                }
            },
            .call => |call_expr| {
                try self.emitCall(expr, call_expr.callee, call_expr.args, null);
            },
            .field => |fld| {
                if (self.checked.resolvedIdentName(expr)) |rname| {
                    try self.emitIdent(rname);
                    return;
                }
                const var_name = self.sourceOf(fld.name);
                if (fld.target.* == .upper_ident) {
                    const adt_name = self.sourceOf(fld.target.upper_ident);
                    if (self.findCheckedVariant(adt_name, var_name)) |found| {
                        try self.emitADTZeroArgVariant(found.aidx, var_name);
                        return;
                    }
                }
                if (self.checked.exprType(expr)) |fty| {
                    if (fty.* == .adt) {
                        const adt_def = &self.checked.adts[fty.adt];
                        if (self.findCheckedVariant(adt_def.name, var_name)) |found| {
                            try self.emitADTZeroArgVariant(found.aidx, var_name);
                            return;
                        }
                    }
                }
                const fname = var_name;
                if (fld.target.* == .index) {
                    const ix_tty = self.checked.exprType(fld.target.index.target);
                    const is_vec_tgt = self.isVecTyOrViewToVec(ix_tty);
                    if (self.tyBackingKind(ix_tty)) |bk| {
                        switch (bk.kind) {
                            .soa => {
                                if (is_vec_tgt) {
                                    try self.w.writeByte('(');
                                    try self.emitExpr(fld.target.index.target);
                                    try self.w.writeAll(").asView().");
                                } else {
                                    try self.emitExpr(fld.target.index.target);
                                    try self.w.writeByte('.');
                                }
                                try self.emitIdent(fname);
                                try self.w.writeByte('[');
                                try self.emitSliceIndexExpr(fld.target.index.idx);
                                try self.w.writeByte(']');
                                return;
                            },
                            .aosoa => |w| {
                                const albl = self.nextLabel();
                                try self.w.print("blk_{d}: {{ const __ac_{d} = ", .{ albl, albl });
                                if (is_vec_tgt) {
                                    try self.w.writeByte('(');
                                    try self.emitExpr(fld.target.index.target);
                                    try self.w.writeAll(").asView()");
                                } else {
                                    try self.emitExpr(fld.target.index.target);
                                }
                                try self.w.print("; const __aa_{d} = __ac_{d}.base_elem + ", .{ albl, albl });
                                try self.emitSliceIndexExpr(fld.target.index.idx);
                                try self.w.print("; break :blk_{d} __ac_{d}.tiles[__aa_{d} / {d}].", .{ albl, albl, albl, w });
                                try self.emitIdent(fname);
                                try self.w.print("[__aa_{d} % {d}]; }}", .{ albl, w });
                                return;
                            },
                            .aos_slice => {},
                        }
                    } else if (is_vec_tgt) {
                        try self.w.writeByte('(');
                        try self.emitExpr(fld.target.index.target);
                        try self.w.writeAll(").asSlice()[");
                        try self.emitSliceIndexExpr(fld.target.index.idx);
                        try self.w.writeAll("].");
                        try self.emitIdent(fname);
                        return;
                    }
                }
                if (std.mem.eql(u8, fname, "len")) {
                    if (self.checked.exprType(fld.target)) |ftty| {
                        const dinner: *const sema.Ty = switch (ftty.*) {
                            .view => |v| v.target,
                            .path_borrow => |pb| pb.base,
                            else => ftty,
                        };
                        if (isOwnedDynamicTy(dinner)) {
                            try self.w.writeAll("@as(u64, @intCast((");
                            try self.emitExpr(fld.target);
                            try self.w.writeAll(").len))");
                            return;
                        }
                    }
                }
                if (self.checked.exprType(fld.target)) |tty| {
                    if (recordRecordIdxOfTy(tty)) |ridx| {
                        const rec = self.checked.records[ridx];
                        if (findRecordFieldIdx(&rec, fname)) |fidx| {
                            if (fieldBinByte(&rec, fidx)) |bbyte| {
                                try self.emitExpr(fld.target);
                                try self.w.print(".__bin_{d}.", .{bbyte});
                                try self.emitIdent(fname);
                                return;
                            }
                        }
                    }
                }
                try self.emitExpr(fld.target);
                try self.w.writeByte('.');
                try self.emitIdent(fname);
            },
            .index => |ix| {
                const ix_tty = self.checked.exprType(ix.target);
                if (self.tyBackingKind(ix_tty) != null) {
                    try self.emitExpr(ix.target);
                    if (ix.idx.* == .binary and (ix.idx.binary.op == .range or ix.idx.binary.op == .range_eq)) {
                        try self.w.writeAll(".slice(");
                        try self.emitSliceIndexExpr(ix.idx.binary.left);
                        try self.w.writeAll(", ");
                        try self.emitSliceIndexExpr(ix.idx.binary.right);
                        if (ix.idx.binary.op == .range_eq) try self.w.writeAll(" + 1");
                        try self.w.writeByte(')');
                    } else {
                        try self.w.writeAll(".get(");
                        try self.emitSliceIndexExpr(ix.idx);
                        try self.w.writeByte(')');
                    }
                    return;
                }
                if (self.isVecTyOrViewToVec(ix_tty)) {
                    if (ix.idx.* == .binary and (ix.idx.binary.op == .range or ix.idx.binary.op == .range_eq)) {
                        try self.w.writeByte('(');
                        try self.emitExpr(ix.target);
                        try self.w.writeAll(").slice(");
                        try self.emitSliceIndexExpr(ix.idx.binary.left);
                        try self.w.writeAll(", ");
                        try self.emitSliceIndexExpr(ix.idx.binary.right);
                        if (ix.idx.binary.op == .range_eq) try self.w.writeAll(" + 1");
                        try self.w.writeByte(')');
                    } else {
                        try self.w.writeByte('(');
                        try self.emitExpr(ix.target);
                        try self.w.writeAll(").asSlice()[");
                        try self.emitSliceIndexExpr(ix.idx);
                        try self.w.writeByte(']');
                    }
                    return;
                }
                try self.emitExpr(ix.target);
                try self.w.writeByte('[');
                if (ix.idx.* == .binary and (ix.idx.binary.op == .range or ix.idx.binary.op == .range_eq)) {
                    try self.emitSliceIndexExpr(ix.idx.binary.left);
                    try self.w.writeAll("..");
                    try self.emitSliceIndexExpr(ix.idx.binary.right);
                } else {
                    try self.emitSliceIndexExpr(ix.idx);
                }
                try self.w.writeByte(']');
            },
            .try_op => |t| {
                const inner_ty = self.checked.exprType(t.operand);
                if (inner_ty != null and inner_ty.?.* == .option) {
                    try self.w.writeByte('(');
                    try self.emitExpr(t.operand);
                    if (self.current_fn_ret != null and self.current_fn_ret.?.* == .option) {
                        try self.w.writeAll(" orelse return null)");
                    } else {
                        try self.w.writeAll(" orelse @panic(\"unwrap None\"))");
                    }
                } else if (inner_ty != null and inner_ty.?.* == .result) {
                    const r_lbl = self.nextLabel();
                    try self.w.writeAll("(switch (");
                    try self.emitExpr(t.operand);
                    if (self.current_fn_ret != null and self.current_fn_ret.?.* == .result) {
                        try self.w.print(") {{ .Ok => |__ok_{d}| __ok_{d}, .Err => |__err_{d}| return .{{ .Err = __err_{d} }} }})", .{ r_lbl, r_lbl, r_lbl, r_lbl });
                    } else {
                        try self.w.print(") {{ .Ok => |__ok_{d}| __ok_{d}, .Err => @panic(\"unwrap Err\") }})", .{ r_lbl, r_lbl });
                    }
                } else {
                    try self.emitExpr(t.operand);
                }
            },
            .record_lit => |rl| {
                const raw_rname = if (rl.path.len > 0) self.sourceOf(rl.path[rl.path.len - 1]) else "Record";
                const ridx = self.checked.resolvedRecordIdx(expr) orelse self.findCheckedRecordIndex(raw_rname);
                const rname = if (ridx) |ri| self.checked.records[ri].name else raw_rname;
                const lit_ty = self.checked.exprType(expr);
                const has_bins = if (ridx) |ri| (!self.checked.records[ri].is_flat_c and recordHasAnyBin(&self.checked.records[ri])) else false;
                if (lit_ty != null and lit_ty.?.* == .applied and lit_ty.?.applied.args.len > 0) {
                    try self.emitTy(lit_ty.?);
                } else {
                    try self.emitIdent(rname);
                }
                try self.w.writeAll("{ ");
                if (has_bins) {
                    const rec = self.checked.records[ridx.?];
                    var emitted_bins = std.AutoHashMapUnmanaged(usize, void).empty;
                    var wrote_any = false;
                    for (rl.fields) |rf| {
                        const fname = self.sourceOf(rf.name);
                        const fidx = findRecordFieldIdx(&rec, fname);
                        if (fidx != null and fieldBinByte(&rec, fidx.?) != null) {
                            const bbyte = fieldBinByte(&rec, fidx.?).?;
                            if (emitted_bins.contains(bbyte)) continue;
                            emitted_bins.put(self.alloc, bbyte, {}) catch {};
                            if (wrote_any) try self.w.writeAll(", ");
                            wrote_any = true;
                            try self.w.print(".__bin_{d} = .{{ ", .{bbyte});
                            var wrote_bin_fld = false;
                            for (rl.fields) |bf| {
                                const bfname = self.sourceOf(bf.name);
                                const bfidx = findRecordFieldIdx(&rec, bfname) orelse continue;
                                if ((fieldBinByte(&rec, bfidx) orelse continue) != bbyte) continue;
                                if (wrote_bin_fld) try self.w.writeAll(", ");
                                wrote_bin_fld = true;
                                try self.w.writeByte('.');
                                try self.emitIdent(bfname);
                                try self.w.writeAll(" = ");
                                if (bf.value) |val| {
                                    try self.emitCoercedExpr(val, rec.fields[bfidx].ty);
                                } else {
                                    try self.emitIdent(bfname);
                                }
                            }
                            try self.w.writeAll(" }");
                        } else {
                            if (wrote_any) try self.w.writeAll(", ");
                            wrote_any = true;
                            try self.w.writeByte('.');
                            try self.emitIdent(fname);
                            try self.w.writeAll(" = ");
                            const field_ty: ?*const sema.Ty = if (fidx) |fi_val| rec.fields[fi_val].ty else null;
                            if (rf.value) |val| {
                                if (field_ty) |ft| try self.emitCoercedExpr(val, ft) else try self.emitExpr(val);
                            } else {
                                try self.emitIdent(fname);
                            }
                        }
                    }
                } else {
                    for (rl.fields, 0..) |rf, fi| {
                        if (fi > 0) try self.w.writeAll(", ");
                        const fname = self.sourceOf(rf.name);
                        try self.w.writeByte('.');
                        try self.emitIdent(fname);
                        try self.w.writeAll(" = ");
                        var field_ty: ?*const sema.Ty = null;
                        if (ridx) |ri| {
                            for (self.checked.records[ri].fields) |cf| {
                                if (std.mem.eql(u8, cf.name, fname)) {
                                    field_ty = cf.ty;
                                    break;
                                }
                            }
                        }
                        if (rf.value) |val| {
                            if (field_ty) |ft| {
                                try self.emitCoercedExpr(val, ft);
                            } else {
                                try self.emitExpr(val);
                            }
                        } else {
                            try self.emitIdent(fname);
                        }
                    }
                }
                try self.w.writeAll(" }");
            },
            .tuple => |tp| {
                if (tp.elems.len == 0) {
                    try self.w.writeAll("{}");
                } else {
                    try self.w.writeAll(".{ ");
                    for (tp.elems, 0..) |el, i| {
                        if (i > 0) try self.w.writeAll(", ");
                        try self.emitExpr(el);
                    }
                    try self.w.writeAll(" }");
                }
            },
            .list => |ls| {
                const list_ty = self.checked.exprType(expr);
                if (list_ty != null and list_ty.?.* == .vec) {
                    try self.emitVecListLiteral(ls.elems, list_ty.?);
                    return;
                }
                try self.w.writeAll("&[_]");
                if (list_ty != null and list_ty.?.* == .slice) {
                    try self.emitTy(list_ty.?.slice.elem);
                } else {
                    try self.w.writeAll("u64");
                }
                try self.w.writeAll("{ ");
                for (ls.elems, 0..) |el, i| {
                    if (i > 0) try self.w.writeAll(", ");
                    if (list_ty != null and list_ty.?.* == .slice) {
                        try self.emitCoercedExpr(el, list_ty.?.slice.elem);
                    } else {
                        try self.emitExpr(el);
                    }
                }
                try self.w.writeAll(" }");
            },
            .block => |*blk| try self.emitBlockExpr(blk),
            .if_expr => |ie| try self.emitIfExpr(expr, &ie),
            .case_expr => |ce| try self.emitCaseExpr(expr, &ce),
            .lambda => |lam| try self.emitLambdaExpr(expr, &lam),
            .view_expr => |vw| {
                const res_void = self.isVoidExpr(expr);
                const lbl = if (res_void) 0 else self.nextLabel();
                if (res_void) {
                    try self.w.writeAll("{\n");
                } else {
                    try self.w.print("blk_{d}: {{\n", .{lbl});
                }
                self.indent += 1;
                const vsv_mark = self.pushScopeVars();
                defer self.popScopeVars(vsv_mark);
                if (vw.binding) |bspan| {
                    const bn = self.sourceOf(bspan);
                    const tgt_ty = self.checked.exprType(vw.target);
                    const already_ptr = tgt_ty != null and isPointerType(tgt_ty.?);
                    const is_slice_like = tgt_ty != null and (tgt_ty.?.* == .slice or tgt_ty.?.* == .collection or
                        (tgt_ty.?.* == .view and (tgt_ty.?.view.target.* == .slice or tgt_ty.?.view.target.* == .collection)));
                    try self.writeIndent();
                    try self.w.writeAll("const ");
                    try self.emitIdent(bn);
                    try self.w.writeAll(" = ");
                    if (!already_ptr and !is_slice_like) try self.w.writeByte('&');
                    try self.emitExpr(vw.target);
                    try self.w.writeAll(";\n");
                    if (tgt_ty) |tt| {
                        if (already_ptr or is_slice_like) {
                            self.bindScopeVar(bn, tt, vw.mode != .shared);
                        } else if (self.alloc.create(sema.Ty) catch null) |vty| {
                            vty.* = .{ .view = .{ .mode = vw.mode orelse .shared, .target = tt, .target_record = recordRecordIdxOfTy(tt) } };
                            self.bindScopeVar(bn, vty, false);
                        }
                    }
                    if (!self.blockMentionsIdent(&vw.body, bn)) {
                        try self.writeIndent();
                        try self.w.writeAll("_ = ");
                        try self.emitIdent(bn);
                        try self.w.writeAll(";\n");
                    }
                }
                try self.emitStmtsWithRest(vw.body.stmts, vw.body.tail);
                if (vw.body.tail) |t| {
                    if (res_void) {
                        try self.emitTailStmt(t);
                    } else {
                        try self.writeIndent();
                        try self.w.print("break :blk_{d} ", .{lbl});
                        try self.emitExpr(t);
                        try self.w.writeAll(";\n");
                    }
                }
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeByte('}');
            },
            .fork_expr => |fk| {
                if (!fk.is_parallel or fk.branches.len < 2) {
                    try self.w.writeAll("{\n");
                    self.indent += 1;
                    for (fk.branches) |*br| {
                        const bmark = self.pushScopeVars();
                        defer self.popScopeVars(bmark);
                        try self.writeIndent();
                        try self.w.writeAll("{\n");
                        self.indent += 1;
                        try self.emitStmtsWithRest(br.stmts, br.tail);
                        if (br.tail) |t| try self.emitTailStmt(t);
                        self.indent -= 1;
                        try self.writeIndent();
                        try self.w.writeAll("}\n");
                    }
                    self.indent -= 1;
                    try self.writeIndent();
                    try self.w.writeByte('}');
                } else {
                    const fork_id = self.nextLabel();
                    const branch_caps: [][]const ForkCapture = self.alloc.alloc([]const ForkCapture, fk.branches.len) catch &.{};
                    for (fk.branches, 0..) |*br, bi| {
                        if (bi == 0) continue;
                        if (bi < branch_caps.len) {
                            branch_caps[bi] = self.collectFreeCaptures(br) catch &.{};
                        }
                    }

                    try self.w.writeAll("{\n");
                    self.indent += 1;
                    try self.writeIndent();
                    try self.w.print("// @parallel fork/join: spawning {d} OS worker thread(s) via std.Thread\n", .{fk.branches.len - 1});

                    for (fk.branches, 0..) |*br, bi| {
                        if (bi == 0) continue;
                        const caps = if (bi < branch_caps.len) branch_caps[bi] else &.{};
                        try self.writeIndent();
                        try self.w.print("const __ForkWorker_{d}_{d} = struct {{\n", .{ fork_id, bi });
                        self.indent += 1;
                        for (caps) |cap| {
                            try self.writeIndent();
                            try self.emitIdent(cap.name);
                            try self.w.writeAll(": ");
                            if (cap.by_ptr) try self.w.writeByte('*');
                            try self.emitTy(cap.ty);
                            try self.w.writeAll(",\n");
                        }
                        try self.writeIndent();
                        try self.w.writeAll("fn run(__ctx: @This()) void {\n");
                        self.indent += 1;
                        if (caps.len == 0) {
                            try self.writeIndent();
                            try self.w.writeAll("_ = __ctx;\n");
                        }

                        const prev_deref = self.deref_idents;
                        const prev_ctx_vals = self.ctx_value_idents;
                        const prev_scopes = self.scope_vars;
                        var w_deref: std.ArrayList([]const u8) = .empty;
                        var w_ctx_vals: std.ArrayList([]const u8) = .empty;
                        var w_scopes: std.ArrayList(ScopeVar) = .empty;
                        for (caps) |cap| {
                            if (cap.by_ptr) {
                                w_deref.append(self.alloc, cap.name) catch {};
                            } else {
                                w_ctx_vals.append(self.alloc, cap.name) catch {};
                            }
                            w_scopes.append(self.alloc, .{
                                .name = cap.name,
                                .ty = cap.ty,
                                .is_mut = cap.by_ptr,
                            }) catch {};
                        }
                        self.deref_idents = w_deref;
                        self.ctx_value_idents = w_ctx_vals;
                        self.scope_vars = w_scopes;
                        defer {
                            self.deref_idents = prev_deref;
                            self.ctx_value_idents = prev_ctx_vals;
                            self.scope_vars = prev_scopes;
                        }

                        try self.emitStmtsWithRest(br.stmts, br.tail);
                        if (br.tail) |t| try self.emitTailStmt(t);
                        self.indent -= 1;
                        try self.writeIndent();
                        try self.w.writeAll("}\n");
                        self.indent -= 1;
                        try self.writeIndent();
                        try self.w.writeAll("};\n");
                    }

                    for (1..fk.branches.len) |bi| {
                        const caps = if (bi < branch_caps.len) branch_caps[bi] else &.{};
                        try self.writeIndent();
                        try self.w.print("const __thr_{d}_{d} = std.Thread.spawn(.{{}}, __ForkWorker_{d}_{d}.run, .{{__ForkWorker_{d}_{d}{{ ", .{
                            fork_id,
                            bi,
                            fork_id,
                            bi,
                            fork_id,
                            bi,
                        });
                        for (caps, 0..) |cap, ci| {
                            if (ci > 0) try self.w.writeAll(", ");
                            try self.w.writeByte('.');
                            try self.emitIdent(cap.name);
                            try self.w.writeAll(" = ");
                            if (cap.by_ptr) try self.w.writeByte('&');
                            if (self.isDerefIdent(cap.name)) {
                                try self.w.writeAll("(__ctx.");
                                try self.emitIdent(cap.name);
                                try self.w.writeAll(".*)");
                            } else if (self.isCtxValueIdent(cap.name)) {
                                try self.w.writeAll("__ctx.");
                                try self.emitIdent(cap.name);
                            } else {
                                try self.emitIdent(cap.name);
                            }
                        }
                        try self.w.writeAll(" }}) catch @panic(\"parallel fork: thread spawn failed\");\n");
                    }

                    // Branch 0 executes concurrently on the caller thread before joining workers.
                    {
                        const br0 = &fk.branches[0];
                        const bmark = self.pushScopeVars();
                        defer self.popScopeVars(bmark);
                        try self.writeIndent();
                        try self.w.writeAll("{\n");
                        self.indent += 1;
                        try self.emitStmtsWithRest(br0.stmts, br0.tail);
                        if (br0.tail) |t| try self.emitTailStmt(t);
                        self.indent -= 1;
                        try self.writeIndent();
                        try self.w.writeAll("}\n");
                    }

                    for (1..fk.branches.len) |bi| {
                        try self.writeIndent();
                        try self.w.print("__thr_{d}_{d}.join();\n", .{ fork_id, bi });
                    }
                    self.indent -= 1;
                    try self.writeIndent();
                    try self.w.writeByte('}');
                }
            },
            .using_expr => |ue| try self.emitExpr(ue.target),
            .todo_expr => |td| {
                try self.w.writeAll("@panic(");
                if (td.message) |m| try self.emitExpr(m) else try self.w.writeAll("\"todo\"");
                try self.w.writeByte(')');
            },
            .panic_expr => |pn| {
                try self.w.writeAll("@panic(");
                if (pn.message) |m| try self.emitExpr(m) else try self.w.writeAll("\"panic\"");
                try self.w.writeByte(')');
            },
            .err => try self.w.writeAll("{}"),
        }
    }

    fn operandInteger(ty: ?*const sema.Ty) ?int_range.IntType {
        const operand = ty orelse return null;
        return switch (operand.*) {
            .view => |v| v.target.isInteger(),
            else => operand.isInteger(),
        };
    }

    fn emitAssignmentOperand(self: *Emitter, expr: *const ast.Expr, op: ast.AssignOp, target: ?*const sema.Ty) Io.Writer.Error!void {
        if (target) |ty| {
            if (op == .assign and ty.isInteger() != null) {
                try self.emitIntegerOperand(expr, ty);
            } else {
                try self.emitCoercedExpr(expr, ty);
            }
        } else try self.emitExpr(expr);
    }

    fn emitIntegerOperand(self: *Emitter, expr: *const ast.Expr, target: ?*const sema.Ty) Io.Writer.Error!void {
        if (self.checked.exprType(expr)) |ty| {
            if (ty.* == .view) {
                if (ty.view.target.isInteger()) |source| {
                    const integer = if (target) |t| t.isInteger() else null;
                    const cast = if (integer != null and
                        (source.signed != integer.?.signed or source.bits != integer.?.bits))
                        integer
                    else
                        null;
                    if (cast) |t| {
                        try self.w.print("@as({c}{d}, @intCast(", .{
                            if (t.signed) @as(u8, 'i') else @as(u8, 'u'),
                            t.bits,
                        });
                    }
                    try self.w.writeByte('(');
                    try self.emitExpr(expr);
                    try self.w.writeAll(").*");
                    if (cast != null) try self.w.writeAll("))");
                    return;
                }
            }
        }
        if (target) |ty| {
            try self.emitCoercedExpr(expr, ty);
        } else try self.emitExpr(expr);
    }

    fn emitBinary(self: *Emitter, full_expr: *const ast.Expr, b: anytype) Io.Writer.Error!void {
        switch (b.op) {
            .pipe => {
                const pipe = self.flattenCollectionPipeline(full_expr);
                if (pipe.map_stages.len >= 2 or pipe.fold_arg != null) {
                    try self.emitCollectionPipeline(full_expr, pipe, true);
                    return;
                }
                // Fused `opt_or_res |> map(f) |> unwrap_or(default)` without intermediate allocation.
                if (b.right.* == .call and b.right.call.callee.* == .ident and
                    std.mem.eql(u8, self.sourceOf(b.right.call.callee.ident), "unwrap_or") and
                    b.right.call.args.len == 1 and b.left.* == .binary and b.left.binary.op == .pipe and
                    b.left.binary.right.* == .call and b.left.binary.right.call.callee.* == .ident and
                    std.mem.eql(u8, self.sourceOf(b.left.binary.right.call.callee.ident), "map") and
                    b.left.binary.right.call.args.len == 1)
                {
                    const inner_base = b.left.binary.left;
                    const inner_ty = self.checked.exprType(inner_base);
                    if (inner_ty != null and (inner_ty.?.* == .option or inner_ty.?.* == .result)) {
                        try self.emitFusedMapUnwrapOr(
                            full_expr,
                            inner_base,
                            inner_ty.?,
                            b.left.binary.right.call.args[0].value,
                            b.right.call.args[0].value,
                        );
                        return;
                    }
                }
                if (b.right.* == .using_expr) {
                    const ue = b.right.using_expr;
                    if (ue.target.* == .call) {
                        try self.emitCall(ue.target, ue.target.call.callee, ue.target.call.args, b.left);
                    } else {
                        try self.emitCall(null, ue.target, &.{}, b.left);
                    }
                    return;
                }
                if (b.right.* == .call) {
                    try self.emitCall(b.right, b.right.call.callee, b.right.call.args, b.left);
                } else {
                    try self.emitCall(null, b.right, &.{}, b.left);
                }
            },
            .concat => {
                try self.w.writeAll("aethelConcat(");
                try self.emitExpr(b.left);
                try self.w.writeAll(", ");
                try self.emitExpr(b.right);
                try self.w.writeByte(')');
            },
            .eq, .ne, .lt, .le, .gt, .ge => {
                const li = operandInteger(self.checked.exprType(b.left));
                const ri = operandInteger(self.checked.exprType(b.right));
                const l_lit = self.isUnsizedIntLit(b.left) != null;
                const r_lit = self.isUnsizedIntLit(b.right) != null;
                const target: ?sema.Ty = if (li != null and ri != null) .{
                    .int = if (r_lit and !l_lit) li.? else if (l_lit and !r_lit) ri.? else commonIntType(li.?, ri.?),
                } else null;

                try self.w.writeByte('(');
                try self.emitIntegerOperand(b.left, if (target) |*ty| ty else null);
                try self.w.print(" {s} ", .{b.op.symbol()});
                try self.emitIntegerOperand(b.right, if (target) |*ty| ty else null);
                try self.w.writeByte(')');
            },
            .and_op, .or_op => {
                const sym = if (b.op == .and_op) "and" else "or";
                try self.w.writeByte('(');
                try self.emitExpr(b.left);
                try self.w.print(" {s} ", .{sym});
                try self.emitExpr(b.right);
                try self.w.writeByte(')');
            },
            .add_sat, .sub_sat, .mul_sat => {
                const res_ty = self.checked.exprType(full_expr);
                if (res_ty != null and res_ty.?.* == .int_range) {
                    const ir = res_ty.?.int_range;
                    if (ir.range == .bounded and ir.synthesized.bits <= 126) {
                        const bounds = ir.range.bounded;
                        const op_sym: []const u8 = switch (b.op) {
                            .add_sat => "+",
                            .sub_sat => "-",
                            .mul_sat => "*",
                            else => unreachable,
                        };
                        try self.w.print("aethelClamp({c}{d}, (@as(i128, ", .{
                            if (ir.synthesized.signed) @as(u8, 'i') else @as(u8, 'u'),
                            ir.synthesized.bits,
                        });
                        if (b.op == .sub_sat) try self.emitIntegerOperand(b.left, null) else try self.emitExpr(b.left);
                        try self.w.print(") {s} @as(i128, ", .{op_sym});
                        if (b.op == .sub_sat) try self.emitIntegerOperand(b.right, null) else try self.emitExpr(b.right);
                        try self.w.print(")), {d}, {d})", .{ bounds.lo, bounds.hi });
                        return;
                    }
                }
                try self.emitTypedBinOp(full_expr, b.op, b.left, b.right);
            },
            .add_wrap, .sub_wrap, .mul_wrap => {
                try self.emitTypedBinOp(full_expr, b.op, b.left, b.right);
            },
            .add, .sub, .mul, .bit_or, .bit_xor, .bit_and => {
                try self.emitTypedBinOp(full_expr, b.op, b.left, b.right);
            },
            .div, .rem => {
                const res_ty = self.checked.exprType(full_expr);
                const it_opt = if (res_ty) |t| t.isInteger() else null;
                if (it_opt) |it| {
                    if (it.signed) {
                        const c_ty = sema.Ty{ .int = it };
                        const fn_name = if (b.op == .div) "@divTrunc(" else "@rem(";
                        try self.w.writeAll(fn_name);
                        try self.emitCoercedExpr(b.left, &c_ty);
                        try self.w.writeAll(", ");
                        try self.emitCoercedExpr(b.right, &c_ty);
                        try self.w.writeByte(')');
                        return;
                    }
                }
                try self.emitTypedBinOp(full_expr, b.op, b.left, b.right);
            },
            .shl, .shr => {
                const res_ty = self.checked.exprType(full_expr);
                const it_opt = if (res_ty) |t| t.isInteger() else null;
                if (it_opt) |it| {
                    const c_ty = sema.Ty{ .int = it };
                    try self.w.writeByte('(');
                    try self.emitCoercedExpr(b.left, &c_ty);
                    try self.w.print(" {s} @as(std.math.Log2Int({c}{d}), @intCast(", .{
                        b.op.symbol(),
                        if (it.signed) @as(u8, 'i') else @as(u8, 'u'),
                        it.bits,
                    });
                    try self.emitExpr(b.right);
                    try self.w.writeAll(")))");
                    return;
                }
                try self.emitTypedBinOp(full_expr, b.op, b.left, b.right);
            },
            .range, .range_eq => {
                try self.emitExpr(b.left);
            },
        }
    }

    fn intTypeCovers(outer: int_range.IntType, inner: int_range.IntType) bool {
        if (!outer.signed) {
            return !inner.signed and outer.bits >= inner.bits;
        }
        if (inner.signed) {
            return outer.bits >= inner.bits;
        }
        return outer.bits > inner.bits;
    }

    fn emitTypedBinOp(
        self: *Emitter,
        full_expr: *const ast.Expr,
        op: ast.BinaryOp,
        left: *const ast.Expr,
        right: *const ast.Expr,
    ) Io.Writer.Error!void {
        const sym = op.symbol();
        const res_ty = self.checked.exprType(full_expr);
        const lt = self.checked.exprType(left);
        const rt = self.checked.exprType(right);
        const res_it = if (res_ty) |t| t.isInteger() else null;
        const li = if (lt) |t| t.isInteger() else null;
        const ri = if (rt) |t| t.isInteger() else null;

        if (res_it) |target_it| {
            if (op != .add_wrap and op != .sub_wrap and op != .mul_wrap and
                op != .add_sat and op != .sub_sat and op != .mul_sat and
                li != null and ri != null and
                (!intTypeCovers(target_it, li.?) or !intTypeCovers(target_it, ri.?)))
            {
                const base_it = commonIntType(li.?, ri.?);
                const need_signed = base_it.signed or target_it.signed or op == .sub;
                const extra: u16 = if (!base_it.signed and need_signed) 2 else 1;
                const calc_bits: u16 = switch (op) {
                    .add, .sub => @min(@as(u16, 65535), @max(li.?.bits, ri.?.bits) +| extra),
                    .mul => @min(@as(u16, 65535), (li.?.bits +| ri.?.bits) +| (if (need_signed and !base_it.signed) @as(u16, 1) else @as(u16, 0))),
                    else => base_it.bits,
                };
                const calc_it = int_range.IntType{ .signed = need_signed, .bits = calc_bits };
                const calc_ty = sema.Ty{ .int = calc_it };
                try self.w.print("@as({c}{d}, @intCast((", .{
                    if (target_it.signed) @as(u8, 'i') else @as(u8, 'u'),
                    target_it.bits,
                });
                try self.emitCoercedExpr(left, &calc_ty);
                try self.w.print(" {s} ", .{sym});
                try self.emitCoercedExpr(right, &calc_ty);
                try self.w.writeAll(")))");
                return;
            }
            try self.w.writeByte('(');
            if (op == .sub_sat) {
                try self.emitIntegerOperand(left, res_ty);
                try self.w.print(" {s} ", .{sym});
                try self.emitIntegerOperand(right, res_ty);
            } else {
                try self.emitCoercedExpr(left, res_ty.?);
                try self.w.print(" {s} ", .{sym});
                try self.emitCoercedExpr(right, res_ty.?);
            }
            try self.w.writeByte(')');
            return;
        }
        try self.w.writeByte('(');
        try self.emitExpr(left);
        try self.w.print(" {s} ", .{sym});
        try self.emitExpr(right);
        try self.w.writeByte(')');
    }

    fn builtinPrintMode(self: *const Emitter, callee: *const ast.Expr) ?struct { newline: bool, to_stderr: bool } {
        const name: []const u8 = switch (callee.*) {
            .ident => |sp| self.sourceOf(sp),
            .field => |fld| blk: {
                if (fld.target.* == .ident and std.mem.eql(u8, self.sourceOf(fld.target.ident), "io")) {
                    break :blk self.sourceOf(fld.name);
                }
                return null;
            },
            else => return null,
        };
        if (std.mem.eql(u8, name, "println")) return .{ .newline = true, .to_stderr = false };
        if (std.mem.eql(u8, name, "print")) return .{ .newline = false, .to_stderr = false };
        if (std.mem.eql(u8, name, "eprintln")) return .{ .newline = true, .to_stderr = true };
        if (std.mem.eql(u8, name, "eprint")) return .{ .newline = false, .to_stderr = true };
        return null;
    }

    fn emitExternCallbackTrampoline(self: *Emitter, ft: sema.FnTy, arg_val: *const ast.Expr) Io.Writer.Error!void {
        try self.w.writeAll("&((struct {\n");
        self.indent += 1;
        try self.writeIndent();
        try self.w.writeAll("fn __aethel_cb(");
        var first = true;
        for (ft.params, 0..) |cp, ci| {
            if (!first) try self.w.writeAll(", ");
            first = false;
            if (cp.* == .string) {
                try self.w.print("noalias __cb_{d}_ptr: [*]const u8, __cb_{d}_len: usize", .{ ci, ci });
            } else if (cp.* == .slice or (cp.* == .view and cp.view.target.* == .slice)) {
                const mutable = if (cp.* == .slice) cp.slice.mutable else (cp.view.mode == .exclusive and cp.view.target.slice.mutable);
                const elem = if (cp.* == .slice) cp.slice.elem else cp.view.target.slice.elem;
                try self.w.print("noalias __cb_{d}_ptr: [*]", .{ci});
                if (!mutable) try self.w.writeAll("const ");
                try self.emitTy(elem);
                try self.w.print(", __cb_{d}_len: usize", .{ci});
            } else {
                try self.w.print("__cb_{d}: ", .{ci});
                try self.emitTy(cp);
            }
        }
        try self.w.writeAll(") callconv(.c) ");
        const ret_void = isVoidTy(ft.ret);
        if (ret_void) {
            try self.w.writeAll("void");
        } else {
            try self.emitTy(ft.ret);
        }
        try self.w.writeAll(" {\n");
        self.indent += 1;

        if (arg_val.* == .lambda) {
            const lam = arg_val.lambda;
            const prev_ret = self.current_fn_ret;
            const prev_deref = self.deref_idents;
            const prev_ctx_vals = self.ctx_value_idents;
            const prev_scopes = self.scope_vars;
            self.current_fn_ret = ft.ret;
            var w_scopes: std.ArrayList(ScopeVar) = .empty;
            for (lam.params, 0..) |lp, pi| {
                const pname = self.sourceOf(lp.name);
                const cp = if (pi < ft.params.len) ft.params[pi] else lp_blk: {
                    break :lp_blk self.checked.exprType(arg_val) orelse break;
                };
                try self.writeIndent();
                try self.w.writeAll("const ");
                try self.emitIdent(pname);
                try self.w.writeAll(": ");
                try self.emitTy(cp);
                if (cp.* == .string or cp.* == .slice or (cp.* == .view and cp.view.target.* == .slice)) {
                    try self.w.print(" = __cb_{d}_ptr[0..__cb_{d}_len];\n", .{ pi, pi });
                } else {
                    try self.w.print(" = __cb_{d};\n", .{pi});
                }
                w_scopes.append(self.alloc, .{
                    .name = pname,
                    .ty = cp,
                    .is_mut = lp.mutable or isPointerType(cp),
                }) catch {};
                if (!self.blockMentionsIdent(&lam.body, pname)) {
                    try self.writeIndent();
                    try self.w.writeAll("_ = &");
                    try self.emitIdent(pname);
                    try self.w.writeAll(";\n");
                }
            }
            self.deref_idents = .empty;
            self.ctx_value_idents = .empty;
            self.scope_vars = w_scopes;
            defer {
                self.current_fn_ret = prev_ret;
                self.deref_idents = prev_deref;
                self.ctx_value_idents = prev_ctx_vals;
                self.scope_vars = prev_scopes;
            }
            try self.emitStmtsWithRest(lam.body.stmts, lam.body.tail);
            if (lam.body.tail) |t| {
                if (ret_void) {
                    try self.emitTailStmt(t);
                } else {
                    try self.writeIndent();
                    try self.w.writeAll("return ");
                    try self.emitCoercedExpr(t, ft.ret);
                    try self.w.writeAll(";\n");
                }
            }
        } else {
            const target_name: []const u8 = self.checked.resolvedIdentName(arg_val) orelse
                if (arg_val.* == .ident) self.sourceOf(arg_val.ident) else if (arg_val.* == .field) self.sourceOf(arg_val.field.name) else "";
            try self.writeIndent();
            if (!ret_void) {
                try self.w.writeAll("return ");
            }
            if (std.mem.eql(u8, target_name, "main")) {
                try self.w.writeAll("aethel_main");
            } else {
                try self.emitIdent(target_name);
            }
            try self.w.writeByte('(');
            for (ft.params, 0..) |cp, ci| {
                if (ci > 0) try self.w.writeAll(", ");
                if (cp.* == .string or cp.* == .slice or (cp.* == .view and cp.view.target.* == .slice)) {
                    try self.w.print("__cb_{d}_ptr[0..__cb_{d}_len]", .{ ci, ci });
                } else {
                    try self.w.print("__cb_{d}", .{ci});
                }
            }
            try self.w.writeAll(");\n");
        }

        self.indent -= 1;
        try self.writeIndent();
        try self.w.writeAll("}\n");
        self.indent -= 1;
        try self.writeIndent();
        try self.w.writeAll("}).__aethel_cb)");
    }

    fn emitCall(
        self: *Emitter,
        call_expr: ?*const ast.Expr,
        callee: *const ast.Expr,
        args: []const ast.CallArg,
        piped_recv: ?*const ast.Expr,
    ) Io.Writer.Error!void {
        // 1. Built-in I/O (`println`, `print`, `eprintln`, `eprint` and `io.*`)
        if (self.builtinPrintMode(callee)) |pm| {
            try self.w.writeAll("aethelPrint(.{ ");
            var first = true;
            if (piped_recv) |pr| {
                try self.emitExpr(pr);
                first = false;
            }
            for (args) |arg| {
                if (!first) try self.w.writeAll(", ");
                first = false;
                try self.emitExpr(arg.value);
            }
            try self.w.print(" }}, {s}, {s})", .{
                if (pm.newline) "true" else "false",
                if (pm.to_stderr) "true" else "false",
            });
            return;
        }

        // 1a. std/* dynamic containers & string intrinsics
        if (call_expr) |ce| {
            if (self.checked.std_intrinsic_calls.get(ce)) |intr| {
                try self.emitStdIntrinsicCall(intr, args, piped_recv);
                return;
            }
        }

        // 1b. In-place collection pipeline (`fleet |> map_in_place(fn(e) { ... })`)
        if (callee.* == .ident and std.mem.eql(u8, self.sourceOf(callee.ident), "map_in_place") and
            piped_recv != null and args.len == 1 and args[0].value.* == .lambda)
        {
            const pipe = CollectionPipeline{
                .base = piped_recv.?,
                .map_stages = self.alloc.dupe(*const ast.Expr, &.{args[0].value}) catch &.{args[0].value},
                .fold_arg = null,
                .fold_init = null,
            };
            try self.emitCollectionPipeline(call_expr, pipe, call_expr != null);
            return;
        }

        // 1c. Option/Result categorical combinators (`map`, `and_then`, `unwrap_or`, `ok_or`)
        if (callee.* == .ident) {
            const cname = self.sourceOf(callee.ident);
            if ((std.mem.eql(u8, cname, "map") or std.mem.eql(u8, cname, "and_then") or
                std.mem.eql(u8, cname, "unwrap_or") or std.mem.eql(u8, cname, "ok_or")) and
                ((piped_recv != null and args.len == 1) or (piped_recv == null and args.len == 2)))
            {
                const recv_expr = piped_recv orelse args[0].value;
                const comb_val = if (piped_recv != null) args[0].value else args[1].value;
                if (self.checked.exprType(recv_expr)) |rty| {
                    if (rty.* == .option or rty.* == .result) {
                        try self.emitOptionResultCombinator(call_expr, cname, recv_expr, rty, comb_val);
                        return;
                    }
                }
            }
            if ((std.mem.eql(u8, cname, "min") or std.mem.eql(u8, cname, "max")) and piped_recv == null and args.len == 2) {
                try self.w.print("@{s}(", .{cname});
                try self.emitExpr(args[0].value);
                try self.w.writeAll(", ");
                try self.emitExpr(args[1].value);
                try self.w.writeByte(')');
                return;
            }
        }

        // 2. ADT constructor calls (`Moving(12)`, `Status.Moving(12)`, `Ok(...)`, `Err(...)`, `Some(...)`)
        if (callee.* == .upper_ident) {
            const cname = self.sourceOf(callee.upper_ident);
            const call_ty = if (call_expr) |ce| self.checked.exprType(ce) else null;
            if (std.mem.eql(u8, cname, "Some") and args.len == 1) {
                if (call_ty != null and call_ty.?.* == .option and call_ty.?.option.* != .err) {
                    try self.w.writeAll("@as(?");
                    try self.emitTy(call_ty.?.option);
                    try self.w.writeAll(", ");
                    try self.emitCoercedExpr(args[0].value, call_ty.?.option);
                    try self.w.writeByte(')');
                } else {
                    try self.w.writeAll("@as(?@TypeOf(");
                    try self.emitExpr(args[0].value);
                    try self.w.writeAll("), ");
                    try self.emitExpr(args[0].value);
                    try self.w.writeByte(')');
                }
                return;
            }
            if ((std.mem.eql(u8, cname, "Ok") or std.mem.eql(u8, cname, "Err")) and args.len == 1) {
                if (call_ty != null and call_ty.?.* == .result and
                    call_ty.?.result.ok.* != .err and call_ty.?.result.err.* != .err)
                {
                    try self.emitTy(call_ty.?);
                    try self.w.print("{{ .{s} = ", .{cname});
                    const payload_ty = if (std.mem.eql(u8, cname, "Ok")) call_ty.?.result.ok else call_ty.?.result.err;
                    try self.emitCoercedExpr(args[0].value, payload_ty);
                    try self.w.writeAll(" }");
                } else {
                    try self.w.print(".{{ .{s} = ", .{cname});
                    if (args.len > 0) try self.emitExpr(args[0].value) else try self.w.writeAll("{}");
                    try self.w.writeAll(" }");
                }
                return;
            }
            if (self.findCheckedVariant(null, cname)) |found| {
                try self.emitADTConstruct(found.aidx, found.vidx, args);
                return;
            }
        }
        if (callee.* == .field and callee.field.target.* == .upper_ident) {
            const adt_name = self.sourceOf(callee.field.target.upper_ident);
            const var_name = self.sourceOf(callee.field.name);
            if (self.findCheckedVariant(adt_name, var_name)) |found| {
                try self.emitADTConstruct(found.aidx, found.vidx, args);
                return;
            }
        }

        // 3. Regular user / extern function call (including module-qualified, generic comptime args, FFI slices, and closures).
        if (call_expr != null and callee.* == .field) {
            if (self.checked.resolvedCallName(callee) == null) {
                const call_ty = self.checked.exprType(call_expr.?);
                if (call_ty != null and call_ty.?.* == .adt) {
                    const adt_def = &self.checked.adts[call_ty.?.adt];
                    const var_name = self.sourceOf(callee.field.name);
                    if (self.findCheckedVariant(adt_def.name, var_name)) |found| {
                        try self.emitADTConstruct(found.aidx, found.vidx, args);
                        return;
                    }
                }
            }
        }

        const trait_res_opt: ?sema.CallTraitResolution = if (call_expr) |ce| self.checked.call_trait_resolutions.get(ce) else null;
        if (trait_res_opt) |tres| {
            if (tres.kind == .trait_method) {
                const tm = tres.kind.trait_method;
                try self.emitWitnessExpr(tm.witness);
                try self.w.writeByte('.');
                try self.emitIdent(tm.method_name);
                try self.w.writeByte('(');
                var emitted_any = false;
                for (tres.type_args) |ta| {
                    if (emitted_any) try self.w.writeAll(", ");
                    emitted_any = true;
                    try self.emitTy(ta);
                }
                if (piped_recv) |pr| {
                    if (emitted_any) try self.w.writeAll(", ");
                    emitted_any = true;
                    try self.emitCallArg(pr, null);
                }
                for (args) |arg| {
                    if (emitted_any) try self.w.writeAll(", ");
                    emitted_any = true;
                    try self.emitCallArg(arg.value, null);
                }
                try self.w.writeByte(')');
                return;
            }
        }

        const resolved_name = self.checked.resolvedCallName(callee);
        const cf: ?*const sema.CheckedFunction = if (resolved_name) |rn|
            self.findCheckedFn(rn)
        else if (callee.* == .ident)
            self.findCheckedFn(self.sourceOf(callee.ident))
        else
            null;
        if (cf == null) {
            const callee_ty = self.checked.exprType(callee);
            const is_fn_val = (callee_ty != null and callee_ty.?.* == .fn_ty) or
                (callee.* == .ident and self.lookupScopeVar(self.sourceOf(callee.ident)) != null);
            if (is_fn_val) {
                try self.w.writeAll("aethelCall(");
                try self.emitExpr(callee);
                try self.w.writeAll(", .{ ");
                var first_c = true;
                if (piped_recv) |pr| {
                    first_c = false;
                    const p0: ?*const sema.Ty = if (callee_ty != null and callee_ty.?.* == .fn_ty and callee_ty.?.fn_ty.params.len > 0)
                        callee_ty.?.fn_ty.params[0]
                    else
                        null;
                    try self.emitCallArg(pr, p0);
                }
                const r_off: usize = if (piped_recv != null) 1 else 0;
                for (args, 0..) |arg, ai| {
                    if (!first_c) try self.w.writeAll(", ");
                    first_c = false;
                    const pidx = ai + r_off;
                    const pt: ?*const sema.Ty = if (callee_ty != null and callee_ty.?.* == .fn_ty and pidx < callee_ty.?.fn_ty.params.len)
                        callee_ty.?.fn_ty.params[pidx]
                    else
                        null;
                    try self.emitCallArg(arg.value, pt);
                }
                try self.w.writeAll(" })");
                return;
            }
        }

        const total_offset: usize = if (piped_recv != null) 1 else 0;
        var has_ffi_marshaled = false;
        if (cf != null and cf.?.has_extern_abi) {
            for (cf.?.param_types) |pt| {
                if (self.hasExternMarshaledArg(pt)) {
                    has_ffi_marshaled = true;
                    break;
                }
            }
        }

        if (cf != null and cf.?.has_extern_abi and has_ffi_marshaled) {
            const ret_void = isVoidTy(cf.?.ret_type);
            const lbl = self.nextLabel();
            if (ret_void) {
                try self.w.writeAll("{ ");
            } else {
                try self.w.print("blk_{d}: {{ ", .{lbl});
            }
            for (cf.?.param_types, 0..) |pt, pidx| {
                if (!self.hasExternMarshaledArg(pt) or pt.* == .fn_ty) continue;
                const arg_val: *const ast.Expr = if (piped_recv != null and pidx == 0)
                    piped_recv.?
                else if (pidx >= total_offset and (pidx - total_offset) < args.len)
                    args[pidx - total_offset].value
                else
                    continue;
                try self.w.print("const __ffi_{d}_{d}: ", .{ lbl, pidx });
                try self.emitTy(pt);
                try self.w.writeAll(" = ");
                try self.emitCoercedExpr(arg_val, pt);
                try self.w.writeAll("; ");
            }
            if (!ret_void) {
                try self.w.print("break :blk_{d} ", .{lbl});
            }
            try self.emitIdent(cf.?.rust_sym orelse cf.?.name);
            try self.w.writeByte('(');
            var first_arg = true;
            for (cf.?.param_types, 0..) |pt, pidx| {
                const is_sl = pt.* == .slice or (pt.* == .view and pt.view.target.* == .slice);
                if (pt.* == .string) {
                    if (!first_arg) try self.w.writeAll(", ");
                    first_arg = false;
                    try self.w.print("(if (__ffi_{d}_{d}.len == 0) @as([*]const u8, @ptrFromInt(1)) else __ffi_{d}_{d}.ptr), __ffi_{d}_{d}.len", .{ lbl, pidx, lbl, pidx, lbl, pidx });
                } else if (pt.* == .fn_ty) {
                    if (!first_arg) try self.w.writeAll(", ");
                    first_arg = false;
                    const arg_val: ?*const ast.Expr = if (piped_recv != null and pidx == 0)
                        piped_recv.?
                    else if (pidx >= total_offset and (pidx - total_offset) < args.len)
                        args[pidx - total_offset].value
                    else
                        null;
                    if (arg_val) |av| {
                        try self.emitExternCallbackTrampoline(pt.fn_ty, av);
                    } else {
                        try self.w.writeAll("undefined");
                    }
                } else if (is_sl) {
                    if (!first_arg) try self.w.writeAll(", ");
                    first_arg = false;
                    try self.w.print("__ffi_{d}_{d}.ptr, __ffi_{d}_{d}.len", .{ lbl, pidx, lbl, pidx });
                } else if (self.tyBackingKind(pt)) |bk| {
                    switch (bk.kind) {
                        .soa => {
                            const fidxs = self.findPathBorrowFieldIndices(bk.ridx, pt);
                            const rec = &self.checked.records[bk.ridx];
                            for (fidxs) |fi| {
                                if (!first_arg) try self.w.writeAll(", ");
                                first_arg = false;
                                try self.w.print("__ffi_{d}_{d}.", .{ lbl, pidx });
                                try self.emitIdent(rec.fields[fi].name);
                                try self.w.writeAll(".ptr");
                            }
                            if (!first_arg) try self.w.writeAll(", ");
                            first_arg = false;
                            try self.w.print("__ffi_{d}_{d}.len", .{ lbl, pidx });
                        },
                        .aosoa => {
                            if (!first_arg) try self.w.writeAll(", ");
                            first_arg = false;
                            try self.w.print("__ffi_{d}_{d}.tiles.ptr, __ffi_{d}_{d}.base_elem, __ffi_{d}_{d}.len", .{ lbl, pidx, lbl, pidx, lbl, pidx });
                        },
                        .aos_slice => {},
                    }
                } else {
                    if (!first_arg) try self.w.writeAll(", ");
                    first_arg = false;
                    const arg_val: ?*const ast.Expr = if (piped_recv != null and pidx == 0)
                        piped_recv.?
                    else if (pidx >= total_offset and (pidx - total_offset) < args.len)
                        args[pidx - total_offset].value
                    else
                        null;
                    if (arg_val) |av| {
                        try self.emitCallArg(av, pt);
                    }
                }
            }
            try self.w.writeAll("); }");
            return;
        }

        if (cf) |f| {
            try self.emitIdent(if (f.has_extern_abi) (f.rust_sym orelse f.name) else f.name);
        } else {
            try self.emitExpr(callee);
        }
        try self.w.writeByte('(');

        var emitted_any = false;
        if (cf != null and cf.?.type_params.len > 0) {
            const targs = if (call_expr) |ce| self.checked.callTypeArgs(ce) else null;
            for (cf.?.type_params, 0..) |tp, ti| {
                if (emitted_any) try self.w.writeAll(", ");
                emitted_any = true;
                if (targs != null and ti < targs.?.len) {
                    try self.emitTy(targs.?[ti]);
                } else {
                    try self.w.print("__T_{s}", .{tp});
                }
            }
        }
        if (cf != null and (cf.?.hkt_params.len > 0 or cf.?.constraint_count > 0)) {
            for (cf.?.hkt_params, 0..) |hp, hi| {
                if (emitted_any) try self.w.writeAll(", ");
                emitted_any = true;
                const hn: ?[]const u8 = if (trait_res_opt != null and hi < trait_res_opt.?.hkt_args.len) trait_res_opt.?.hkt_args[hi] else hp;
                try self.emitHKTTypeArg(hn);
            }
            if (trait_res_opt) |tres| {
                for (tres.witnesses) |w| {
                    if (emitted_any) try self.w.writeAll(", ");
                    emitted_any = true;
                    try self.emitWitnessExpr(w);
                }
            } else {
                for (0..cf.?.constraint_count) |wi| {
                    if (emitted_any) try self.w.writeAll(", ");
                    emitted_any = true;
                    try self.w.print("__W_{d}", .{wi});
                }
            }
        }
        if (piped_recv) |pr| {
            if (emitted_any) try self.w.writeAll(", ");
            emitted_any = true;
            const param_ty: ?*const sema.Ty = if (cf != null and cf.?.param_types.len > 0) cf.?.param_types[0] else null;
            try self.emitCallArg(pr, param_ty);
        }
        for (args, 0..) |arg, ai| {
            if (emitted_any) try self.w.writeAll(", ");
            emitted_any = true;
            const pidx = ai + total_offset;
            const param_ty: ?*const sema.Ty = if (cf != null and pidx < cf.?.param_types.len) cf.?.param_types[pidx] else null;
            try self.emitCallArg(arg.value, param_ty);
        }
        try self.w.writeByte(')');
    }

    fn emitHKTTypeArg(self: *Emitter, hname: ?[]const u8) Io.Writer.Error!void {
        const hn = hname orelse "Option";
        if (std.mem.eql(u8, hn, "Option")) {
            try self.w.writeAll("struct { fn apply(comptime __A: type) type { return ?__A; } }.apply");
            return;
        }
        if (std.mem.eql(u8, hn, "f") or std.mem.eql(u8, hn, "g") or (hn.len > 0 and hn[0] >= 'a' and hn[0] <= 'z')) {
            try self.w.print("__F_{s}", .{hn});
            return;
        }
        try self.w.print("struct {{ fn apply(comptime __A: type) type {{ return {s}(__A); }} }}.apply", .{hn});
    }

    fn emitWitnessExpr(self: *Emitter, w: sema.ResolvedWitness) Io.Writer.Error!void {
        switch (w) {
            .param => |pidx| try self.w.print("__W_{d}", .{pidx}),
            .concrete => |cw| {
                const inst = self.checked.instances[cw.inst_idx];
                try self.w.print("__Inst_{s}", .{inst.name});
                const is_generic = inst.type_params.len > 0 or inst.hkt_params.len > 0 or inst.constraints.len > 0;
                if (is_generic) {
                    try self.w.writeByte('(');
                    var comma = false;
                    for (cw.type_args) |ta| {
                        if (comma) try self.w.writeAll(", ");
                        comma = true;
                        try self.emitTy(ta);
                    }
                    for (inst.hkt_params) |hp| {
                        if (comma) try self.w.writeAll(", ");
                        comma = true;
                        try self.emitHKTTypeArg(hp);
                    }
                    for (cw.sub_witnesses) |sw| {
                        if (comma) try self.w.writeAll(", ");
                        comma = true;
                        try self.emitWitnessExpr(sw);
                    }
                    try self.w.writeByte(')');
                }
            },
        }
    }

    fn emitStdIntrinsicRecv(
        self: *Emitter,
        args: []const ast.CallArg,
        piped_recv: ?*const ast.Expr,
    ) Io.Writer.Error!void {
        const recv_expr = piped_recv orelse args[0].value;
        try self.w.writeByte('(');
        try self.emitExpr(recv_expr);
        try self.w.writeByte(')');
    }

    fn emitStdIntrinsicCall(
        self: *Emitter,
        intr: sema.StdIntrinsicCall,
        args: []const ast.CallArg,
        piped_recv: ?*const ast.Expr,
    ) Io.Writer.Error!void {
        const roff: usize = if (piped_recv != null) 0 else 1;
        const is_layout_vec = intr.container_ty.* == .vec and self.tyBackingKind(intr.container_ty) != null;
        switch (intr.kind) {
            .vec_new, .map_new, .set_new, .deque_new => {
                try self.emitTy(intr.container_ty);
                try self.w.writeAll(".new()");
            },
            .vec_with_capacity, .map_with_capacity, .set_with_capacity, .deque_with_capacity => {
                try self.emitTy(intr.container_ty);
                try self.w.writeAll(".withCapacity(@as(u64, @intCast(");
                try self.emitExpr(args[0].value);
                try self.w.writeAll(")))");
            },
            .vec_len, .map_len, .set_len, .deque_len => {
                try self.w.writeAll("@as(u64, @intCast(");
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".len))");
            },
            .vec_capacity => {
                if (self.tyBackingKind(intr.container_ty)) |bk| {
                    switch (bk.kind) {
                        .aosoa => |w| {
                            try self.w.writeAll("@as(u64, @intCast(");
                            try self.emitStdIntrinsicRecv(args, piped_recv);
                            try self.w.print(".tile_cap * {d}))", .{w});
                            return;
                        },
                        else => {},
                    }
                }
                try self.w.writeAll("@as(u64, @intCast(");
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".cap))");
            },
            .vec_is_empty, .map_is_empty, .set_is_empty, .deque_is_empty => {
                try self.w.writeByte('(');
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".len == 0)");
            },
            .vec_push => {
                const elem_ty = intr.container_ty.vec.elem_ty;
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".push(");
                try self.emitCoercedExpr(args[roff].value, elem_ty);
                try self.w.writeByte(')');
            },
            .vec_pop => {
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".pop()");
            },
            .vec_get => {
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(if (is_layout_vec) ".getOpt(@as(u64, @intCast(" else ".get(@as(u64, @intCast(");
                try self.emitExpr(args[roff].value);
                try self.w.writeAll(")))");
            },
            .vec_set => {
                const elem_ty = intr.container_ty.vec.elem_ty;
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(if (is_layout_vec) ".setChecked(@as(u64, @intCast(" else ".set(@as(u64, @intCast(");
                try self.emitExpr(args[roff].value);
                try self.w.writeAll(")), ");
                try self.emitCoercedExpr(args[roff + 1].value, elem_ty);
                try self.w.writeByte(')');
            },
            .vec_swap_remove => {
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".swapRemove(@as(u64, @intCast(");
                try self.emitExpr(args[roff].value);
                try self.w.writeAll(")))");
            },
            .vec_reserve => {
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".reserve(@as(u64, @intCast(");
                try self.emitExpr(args[roff].value);
                try self.w.writeAll(")))");
            },
            .vec_clear, .map_clear, .set_clear, .deque_clear => {
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".clear()");
            },
            .vec_as_slice => {
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".asSlice()");
            },
            .vec_as_mut_slice => {
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".mutSlice()");
            },
            .vec_as_collection => {
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(if (is_layout_vec) ".asView()" else ".asSlice()");
            },
            .map_insert => {
                const kv = intr.container_ty.map;
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".insert(");
                try self.emitCoercedExpr(args[roff].value, kv.key_ty);
                try self.w.writeAll(", ");
                try self.emitCoercedExpr(args[roff + 1].value, kv.val_ty);
                try self.w.writeByte(')');
            },
            .map_put => {
                const kv = intr.container_ty.map;
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".put(");
                try self.emitCoercedExpr(args[roff].value, kv.key_ty);
                try self.w.writeAll(", ");
                try self.emitCoercedExpr(args[roff + 1].value, kv.val_ty);
                try self.w.writeByte(')');
            },
            .map_get => {
                const kv = intr.container_ty.map;
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".get(");
                try self.emitCoercedExpr(args[roff].value, kv.key_ty);
                try self.w.writeByte(')');
            },
            .map_contains => {
                const kv = intr.container_ty.map;
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".contains(");
                try self.emitCoercedExpr(args[roff].value, kv.key_ty);
                try self.w.writeByte(')');
            },
            .map_remove => {
                const kv = intr.container_ty.map;
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".remove(");
                try self.emitCoercedExpr(args[roff].value, kv.key_ty);
                try self.w.writeByte(')');
            },
            .set_insert => {
                const et = intr.container_ty.set.elem_ty;
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".insert(");
                try self.emitCoercedExpr(args[roff].value, et);
                try self.w.writeByte(')');
            },
            .set_contains => {
                const et = intr.container_ty.set.elem_ty;
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".contains(");
                try self.emitCoercedExpr(args[roff].value, et);
                try self.w.writeByte(')');
            },
            .set_remove => {
                const et = intr.container_ty.set.elem_ty;
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".remove(");
                try self.emitCoercedExpr(args[roff].value, et);
                try self.w.writeByte(')');
            },
            .deque_push_back => {
                const et = intr.container_ty.deque.elem_ty;
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".pushBack(");
                try self.emitCoercedExpr(args[roff].value, et);
                try self.w.writeByte(')');
            },
            .deque_push_front => {
                const et = intr.container_ty.deque.elem_ty;
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".pushFront(");
                try self.emitCoercedExpr(args[roff].value, et);
                try self.w.writeByte(')');
            },
            .deque_pop_front => {
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".popFront()");
            },
            .deque_pop_back => {
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".popBack()");
            },
            .deque_get => {
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".get(@as(u64, @intCast(");
                try self.emitExpr(args[roff].value);
                try self.w.writeAll(")))");
            },
            .str_len => {
                try self.w.writeAll("@as(u64, @intCast(");
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".len))");
            },
            .str_is_empty => {
                try self.w.writeByte('(');
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(".len == 0)");
            },
            .str_eq => {
                try self.w.writeAll("std.mem.eql(u8, ");
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(", ");
                try self.emitExpr(args[roff].value);
                try self.w.writeByte(')');
            },
            .str_concat => {
                try self.w.writeAll("aethelConcat(");
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(", ");
                try self.emitExpr(args[roff].value);
                try self.w.writeByte(')');
            },
            .str_repeat => {
                try self.w.writeAll("aethelStrRepeat(");
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(", @as(u64, @intCast(");
                try self.emitExpr(args[roff].value);
                try self.w.writeAll(")))");
            },
            .str_starts_with => {
                try self.w.writeAll("aethelStrStartsWith(");
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(", ");
                try self.emitExpr(args[roff].value);
                try self.w.writeByte(')');
            },
            .str_ends_with => {
                try self.w.writeAll("aethelStrEndsWith(");
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(", ");
                try self.emitExpr(args[roff].value);
                try self.w.writeByte(')');
            },
            .str_contains => {
                try self.w.writeAll("aethelStrContains(");
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(", ");
                try self.emitExpr(args[roff].value);
                try self.w.writeByte(')');
            },
            .str_byte_at => {
                try self.w.writeAll("aethelStrByteAt(");
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(", @as(u64, @intCast(");
                try self.emitExpr(args[roff].value);
                try self.w.writeAll(")))");
            },
            .str_slice_bytes => {
                try self.w.writeAll("aethelStrSlice(");
                try self.emitStdIntrinsicRecv(args, piped_recv);
                try self.w.writeAll(", @as(u64, @intCast(");
                try self.emitExpr(args[roff].value);
                try self.w.writeAll(")), @as(u64, @intCast(");
                try self.emitExpr(args[roff + 1].value);
                try self.w.writeAll(")))");
            },
        }
    }

    fn emitCallArg(self: *Emitter, val: *const ast.Expr, expected: ?*const sema.Ty) Io.Writer.Error!void {
        if (expected) |ep| {
            if (isPointerType(ep)) {
                const vty = self.checked.exprType(val);
                if (vty == null or !isPointerType(vty.?)) {
                    try self.w.writeByte('&');
                    try self.emitExpr(val);
                    return;
                }
                try self.emitExpr(val);
                return;
            }
            try self.emitCoercedExpr(val, ep);
            return;
        }
        try self.emitExpr(val);
    }

    fn emitPackCompactPayload(
        self: *Emitter,
        val_expr: *const ast.Expr,
        ft: *const sema.Ty,
        max_pay_bits: u16,
    ) Io.Writer.Error!void {
        if (ft.* == .bool) {
            try self.w.print("@as(u{d}, @intFromBool(", .{max_pay_bits});
            try self.emitExpr(val_expr);
            try self.w.writeAll("))");
            return;
        }
        const it = ft.isInteger() orelse {
            try self.w.print("@as(u{d}, @intCast(", .{max_pay_bits});
            try self.emitExpr(val_expr);
            try self.w.writeAll("))");
            return;
        };
        if (it.signed) {
            try self.w.print("@as(u{d}, @as(u{d}, @bitCast(", .{ max_pay_bits, it.bits });
            try self.emitCoercedExpr(val_expr, ft);
            try self.w.writeAll(")))");
        } else if (it.bits < max_pay_bits) {
            try self.w.print("@as(u{d}, ", .{max_pay_bits});
            try self.emitCoercedExpr(val_expr, ft);
            try self.w.writeByte(')');
        } else {
            try self.emitCoercedExpr(val_expr, ft);
        }
    }

    fn emitUnpackCompactPayload(
        self: *Emitter,
        adt_id: usize,
        ft: *const sema.Ty,
        max_pay_bits: u16,
    ) Io.Writer.Error!void {
        if (ft.* == .bool) {
            try self.w.print("((__adt_{d}.payload & 1) != 0)", .{adt_id});
            return;
        }
        const it = ft.isInteger() orelse {
            try self.w.print("__adt_{d}.payload", .{adt_id});
            return;
        };
        if (it.signed) {
            if (it.bits < max_pay_bits) {
                try self.w.print("@as(i{d}, @bitCast(@as(u{d}, @truncate(__adt_{d}.payload))))", .{ it.bits, it.bits, adt_id });
            } else {
                try self.w.print("@as(i{d}, @bitCast(__adt_{d}.payload))", .{ it.bits, adt_id });
            }
        } else if (it.bits < max_pay_bits) {
            try self.w.print("@as(u{d}, @truncate(__adt_{d}.payload))", .{ it.bits, adt_id });
        } else {
            try self.w.print("__adt_{d}.payload", .{adt_id});
        }
    }

    fn emitADTZeroArgVariant(self: *Emitter, aidx: usize, var_name: []const u8) Io.Writer.Error!void {
        const adt_def = &self.checked.adts[aidx];
        if (isPureEnumADT(adt_def)) {
            try self.emitIdent(adt_def.name);
            try self.w.writeByte('.');
            try self.emitIdent(var_name);
        } else if (isCompactPackedADT(adt_def)) {
            try self.emitIdent(adt_def.name);
            try self.w.writeAll("{ .tag = .");
            try self.emitIdent(var_name);
            try self.w.writeAll(", .payload = 0 }");
        } else {
            try self.emitIdent(adt_def.name);
            try self.w.writeAll("{ .");
            try self.emitIdent(var_name);
            try self.w.writeAll(" = {} }");
        }
    }

    fn emitADTConstruct(self: *Emitter, aidx: usize, vidx: usize, args: []const ast.CallArg) Io.Writer.Error!void {
        const adt_def = &self.checked.adts[aidx];
        const variant = adt_def.variants[vidx];
        if (isPureEnumADT(adt_def)) {
            try self.emitIdent(adt_def.name);
            try self.w.writeByte('.');
            try self.emitIdent(variant.name);
            return;
        }
        if (isCompactPackedADT(adt_def)) {
            try self.emitIdent(adt_def.name);
            try self.w.writeAll("{ .tag = .");
            try self.emitIdent(variant.name);
            try self.w.writeAll(", .payload = ");
            if (variant.field_types.len == 1 and args.len > 0) {
                try self.emitPackCompactPayload(args[0].value, variant.field_types[0], adt_def.adt_layout.max_payload_bits);
            } else {
                try self.w.writeByte('0');
            }
            try self.w.writeAll(" }");
            return;
        }
        try self.emitIdent(adt_def.name);
        try self.w.writeAll("{ .");
        try self.emitIdent(variant.name);
        try self.w.writeAll(" = ");
        if (variant.field_types.len == 0) {
            try self.w.writeAll("{}");
        } else if (variant.field_types.len == 1) {
            if (args.len > 0) {
                try self.emitCoercedExpr(args[0].value, variant.field_types[0]);
            } else {
                try self.w.writeAll("{}");
            }
        } else {
            try self.w.writeAll(".{ ");
            for (args, 0..) |arg, ai| {
                if (ai > 0) try self.w.writeAll(", ");
                if (ai < variant.field_types.len) {
                    try self.emitCoercedExpr(arg.value, variant.field_types[ai]);
                } else {
                    try self.emitExpr(arg.value);
                }
            }
            try self.w.writeAll(" }");
        }
        try self.w.writeAll(" }");
    }

    fn emitBlockExpr(self: *Emitter, blk: *const ast.Block) Io.Writer.Error!void {
        const bsv_mark = self.pushScopeVars();
        defer self.popScopeVars(bsv_mark);
        const is_void = if (blk.tail) |t| self.isVoidExpr(t) else true;
        if (is_void) {
            try self.w.writeAll("{\n");
            self.indent += 1;
            try self.emitStmtsWithRest(blk.stmts, blk.tail);
            if (blk.tail) |t| try self.emitTailStmt(t);
            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeByte('}');
            return;
        }
        const lbl = self.nextLabel();
        try self.w.print("blk_{d}: {{\n", .{lbl});
        self.indent += 1;
        try self.emitStmtsWithRest(blk.stmts, blk.tail);
        try self.writeIndent();
        try self.w.print("break :blk_{d} ", .{lbl});
        if (blk.tail) |t| try self.emitExpr(t);
        try self.w.writeAll(";\n");
        self.indent -= 1;
        try self.writeIndent();
        try self.w.writeByte('}');
    }

    fn emitIfExpr(self: *Emitter, full_expr: *const ast.Expr, ie: anytype) Io.Writer.Error!void {
        const res_ty = self.checked.exprType(full_expr);
        const res_void = if (res_ty) |rt| isVoidTy(rt) else self.isVoidExpr(full_expr);
        try self.w.writeAll("if (");
        try self.emitExpr(ie.cond);
        try self.w.writeAll(") ");
        if (!res_void and ie.else_branch != null) {
            const lbl = self.nextLabel();
            try self.w.print("blk_{d}: {{\n", .{lbl});
            self.indent += 1;
            try self.emitStmtsWithRest(ie.then_block.stmts, ie.then_block.tail);
            try self.writeIndent();
            try self.w.print("break :blk_{d} ", .{lbl});
            if (ie.then_block.tail) |t| {
                if (res_ty) |rt| try self.emitCoercedExpr(t, rt) else try self.emitExpr(t);
            } else {
                try self.w.writeAll("{}");
            }
            try self.w.writeAll(";\n");
            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeAll("} else ");
            const eb = ie.else_branch.?;
            if (eb.* == .block) {
                const el_lbl = self.nextLabel();
                try self.w.print("blk_{d}: {{\n", .{el_lbl});
                self.indent += 1;
                try self.emitStmtsWithRest(eb.block.stmts, eb.block.tail);
                try self.writeIndent();
                try self.w.print("break :blk_{d} ", .{el_lbl});
                if (eb.block.tail) |t| {
                    if (res_ty) |rt| try self.emitCoercedExpr(t, rt) else try self.emitExpr(t);
                } else {
                    try self.w.writeAll("{}");
                }
                try self.w.writeAll(";\n");
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeByte('}');
            } else {
                if (res_ty) |rt| try self.emitCoercedExpr(eb, rt) else try self.emitExpr(eb);
            }
        } else {
            try self.w.writeAll("{\n");
            self.indent += 1;
            try self.emitStmtsWithRest(ie.then_block.stmts, ie.then_block.tail);
            if (ie.then_block.tail) |t| try self.emitTailStmt(t);
            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeByte('}');
            if (ie.else_branch) |eb| {
                try self.w.writeAll(" else ");
                if (eb.* == .if_expr) {
                    try self.emitExpr(eb);
                } else if (eb.* == .block) {
                    try self.w.writeAll("{\n");
                    self.indent += 1;
                    try self.emitStmtsWithRest(eb.block.stmts, eb.block.tail);
                    if (eb.block.tail) |t| try self.emitTailStmt(t);
                    self.indent -= 1;
                    try self.writeIndent();
                    try self.w.writeByte('}');
                } else {
                    try self.w.writeAll("{\n");
                    self.indent += 1;
                    try self.emitTailStmt(eb);
                    self.indent -= 1;
                    try self.writeIndent();
                    try self.w.writeByte('}');
                }
            }
        }
    }

    fn isSimpleSwitchPat(self: *const Emitter, pat: *const ast.Pattern) bool {
        return switch (pat.*) {
            .wildcard, .ident => true,
            .literal => |lit| lit.tok.tag == .int_literal or lit.tok.tag == .kw_true or lit.tok.tag == .kw_false,
            .range => |rg| self.isSimpleSwitchPat(rg.lo) and self.isSimpleSwitchPat(rg.hi) and rg.inclusive,
            .constructor => |c| blk: {
                for (c.args) |a| {
                    if (a.pattern.* != .ident and a.pattern.* != .wildcard) break :blk false;
                }
                break :blk true;
            },
            .or_pat => |op| blk: {
                for (op.alternatives) |a| {
                    if (!self.isSimpleSwitchPat(a)) break :blk false;
                }
                break :blk true;
            },
            else => false,
        };
    }

    fn canUseZigSwitch(self: *const Emitter, ce: anytype) bool {
        if (ce.subjects.len != 1) return false;
        const sub_ty = self.checked.exprType(ce.subjects[0]);
        if (sub_ty != null and (sub_ty.?.* == .string or sub_ty.?.* == .option)) return false;
        for (ce.arms) |arm| {
            if (arm.guard != null) return false;
            if (arm.alternatives.len == 0) return false;
            for (arm.alternatives) |row| {
                if (row.len != 1) return false;
                const p = row[0];
                if (!self.isSimpleSwitchPat(p)) return false;
                if (p.* == .wildcard or p.* == .ident) {
                    if (arm.alternatives.len > 1) return false;
                }
                if (p.* == .constructor and p.constructor.args.len > 0 and arm.alternatives.len > 1) {
                    return false;
                }
            }
        }
        return true;
    }

    fn canUseOptionIf(self: *const Emitter, ce: anytype) bool {
        if (ce.subjects.len != 1) return false;
        for (ce.arms) |arm| {
            if (arm.guard != null) return false;
            if (arm.alternatives.len == 0) return false;
            for (arm.alternatives) |row| {
                if (row.len != 1) return false;
                if (!self.isSimpleSwitchPat(row[0])) return false;
            }
        }
        return true;
    }

    fn evalSwitchInt(self: *const Emitter, pat: *const ast.Pattern) ?i128 {
        if (pat.* != .literal) return null;
        const lit = pat.literal;
        if (lit.tok.tag != .int_literal) return null;
        const parsed = int_range.parseIntLiteral(self.sourceOf(ast.Span.fromLoc(lit.tok.loc))) orelse return null;
        if (!lit.negative) {
            if (parsed.value > @as(u128, @intCast(std.math.maxInt(i128)))) return null;
            return @intCast(parsed.value);
        }
        if (parsed.value == @as(u128, 1) << 127) return std.math.minInt(i128);
        if (parsed.value > @as(u128, @intCast(std.math.maxInt(i128)))) return null;
        return -@as(i128, @intCast(parsed.value));
    }

    const SwitchIntInterval = struct { lo: i128, hi: i128 };

    fn collectSwitchIntervals(self: *const Emitter, pat: *const ast.Pattern, list: *std.ArrayList(SwitchIntInterval)) void {
        switch (pat.*) {
            .literal => {
                if (self.evalSwitchInt(pat)) |v| {
                    list.append(self.alloc, .{ .lo = v, .hi = v }) catch {};
                }
            },
            .range => |rg| {
                const lo_v = self.evalSwitchInt(rg.lo) orelse return;
                const hi_v = self.evalSwitchInt(rg.hi) orelse return;
                if (lo_v <= hi_v) {
                    list.append(self.alloc, .{ .lo = lo_v, .hi = hi_v }) catch {};
                }
            },
            .or_pat => |op| {
                for (op.alternatives) |alt| self.collectSwitchIntervals(alt, list);
            },
            else => {},
        }
    }

    fn zigIntSwitchComplete(self: *const Emitter, sub_ty: *const sema.Ty, arms: anytype) bool {
        const full_dom: int_range.IntRange = switch (sub_ty.*) {
            .int => |it| int_range.IntRange.ofType(it),
            .int_range => |ir| int_range.IntRange.ofType(ir.synthesized),
            else => return false,
        };
        if (full_dom != .bounded) return false;
        const dom = full_dom.bounded;
        var intervals: std.ArrayList(SwitchIntInterval) = .empty;
        for (arms) |arm| {
            for (arm.alternatives) |row| {
                if (row.len == 1) {
                    self.collectSwitchIntervals(row[0], &intervals);
                }
            }
        }
        std.mem.sort(SwitchIntInterval, intervals.items, {}, struct {
            fn lessThan(_: void, a: SwitchIntInterval, b: SwitchIntInterval) bool {
                if (a.lo != b.lo) return a.lo < b.lo;
                return a.hi < b.hi;
            }
        }.lessThan);
        var cur: i128 = dom.lo;
        for (intervals.items) |iv| {
            if (iv.hi < cur) continue;
            if (iv.lo > cur) return false;
            if (iv.hi >= dom.hi) return true;
            cur = iv.hi + 1;
        }
        return false;
    }

    fn emitOptionCaseExpr(
        self: *Emitter,
        full_expr: *const ast.Expr,
        ce: anytype,
        inner_ty: *const sema.Ty,
        sub_ty: *const sema.Ty,
    ) Io.Writer.Error!void {
        const res_ty = self.checked.exprType(full_expr);
        const res_void = if (res_ty) |rt| isVoidTy(rt) else true;

        var some_body: ?*const ast.Expr = null;
        var some_bind: ?[]const u8 = null;
        var some_whole_bind: ?[]const u8 = null;
        var none_body: ?*const ast.Expr = null;
        var none_whole_bind: ?[]const u8 = null;

        for (ce.arms) |arm| {
            for (arm.alternatives) |row| {
                if (row.len != 1) continue;
                var stack_buf: [16]*const ast.Pattern = undefined;
                var stack_len: usize = 0;
                if (row[0].* == .or_pat) {
                    for (row[0].or_pat.alternatives) |alt| {
                        if (stack_len < stack_buf.len) {
                            stack_buf[stack_len] = alt;
                            stack_len += 1;
                        }
                    }
                } else {
                    stack_buf[0] = row[0];
                    stack_len = 1;
                }
                for (stack_buf[0..stack_len]) |p| {
                    switch (p.*) {
                        .wildcard => {
                            if (some_body == null) some_body = arm.body;
                            if (none_body == null) none_body = arm.body;
                        },
                        .ident => |id| {
                            const vn = self.sourceOf(id.name);
                            if (some_body == null) {
                                some_body = arm.body;
                                some_whole_bind = vn;
                            }
                            if (none_body == null) {
                                none_body = arm.body;
                                none_whole_bind = vn;
                            }
                        },
                        .constructor => |c| {
                            const vn = if (c.path.len > 0) self.sourceOf(c.path[c.path.len - 1]) else "";
                            if (std.mem.eql(u8, vn, "Some")) {
                                if (some_body == null) {
                                    some_body = arm.body;
                                    if (c.args.len > 0 and c.args[0].pattern.* == .ident) {
                                        some_bind = self.sourceOf(c.args[0].pattern.ident.name);
                                    }
                                }
                            } else if (std.mem.eql(u8, vn, "None")) {
                                if (none_body == null) none_body = arm.body;
                            }
                        },
                        else => {},
                    }
                }
            }
        }

        const opt_lbl = self.nextLabel();
        if (res_void) {
            try self.w.writeAll("{\n");
        } else {
            try self.w.print("blk_{d}: {{\n", .{opt_lbl});
        }
        self.indent += 1;
        try self.writeIndent();
        try self.w.print("const __opt_{d} = ", .{opt_lbl});
        try self.emitExpr(ce.subjects[0]);
        try self.w.writeAll(";\n");

        try self.writeIndent();
        const use_capture = some_bind != null and some_body != null and self.exprMentionsIdent(some_body.?, some_bind.?);
        if (use_capture) {
            try self.w.print("if (__opt_{d}) |", .{opt_lbl});
            try self.emitIdent(some_bind.?);
            try self.w.writeAll("| {\n");
        } else {
            try self.w.print("if (__opt_{d} != null) {{\n", .{opt_lbl});
        }
        self.indent += 1;
        {
            const sv = self.pushScopeVars();
            defer self.popScopeVars(sv);
            if (use_capture) {
                self.bindScopeVar(some_bind.?, inner_ty, false);
            }
            if (some_whole_bind) |wb| {
                try self.writeIndent();
                try self.w.writeAll("const ");
                try self.emitIdent(wb);
                try self.w.print(" = __opt_{d};\n", .{opt_lbl});
                self.bindScopeVar(wb, sub_ty, false);
                if (some_body == null or !self.exprMentionsIdent(some_body.?, wb)) {
                    try self.writeIndent();
                    try self.w.writeAll("_ = ");
                    try self.emitIdent(wb);
                    try self.w.writeAll(";\n");
                }
            }
            try self.writeIndent();
            if (some_body) |sb| {
                if (res_void) {
                    if (self.isVoidExpr(sb)) {
                        try self.emitExpr(sb);
                        if (!self.isBlockLikeVoidExpr(sb)) try self.w.writeByte(';');
                        try self.w.writeByte('\n');
                    } else {
                        try self.w.writeAll("_ = ");
                        try self.emitExpr(sb);
                        try self.w.writeAll(";\n");
                    }
                } else {
                    try self.w.print("break :blk_{d} ", .{opt_lbl});
                    if (res_ty) |rt| try self.emitCoercedExpr(sb, rt) else try self.emitExpr(sb);
                    try self.w.writeAll(";\n");
                }
            } else {
                try self.w.writeAll("unreachable;\n");
            }
        }
        self.indent -= 1;
        try self.writeIndent();
        try self.w.writeAll("} else {\n");
        self.indent += 1;
        {
            const nsv = self.pushScopeVars();
            defer self.popScopeVars(nsv);
            if (none_whole_bind) |wb| {
                try self.writeIndent();
                try self.w.writeAll("const ");
                try self.emitIdent(wb);
                try self.w.print(" = __opt_{d};\n", .{opt_lbl});
                self.bindScopeVar(wb, sub_ty, false);
                if (none_body == null or !self.exprMentionsIdent(none_body.?, wb)) {
                    try self.writeIndent();
                    try self.w.writeAll("_ = ");
                    try self.emitIdent(wb);
                    try self.w.writeAll(";\n");
                }
            }
            try self.writeIndent();
            if (none_body) |nb| {
                if (res_void) {
                    if (self.isVoidExpr(nb)) {
                        try self.emitExpr(nb);
                        if (!self.isBlockLikeVoidExpr(nb)) try self.w.writeByte(';');
                        try self.w.writeByte('\n');
                    } else {
                        try self.w.writeAll("_ = ");
                        try self.emitExpr(nb);
                        try self.w.writeAll(";\n");
                    }
                } else {
                    try self.w.print("break :blk_{d} ", .{opt_lbl});
                    if (res_ty) |rt| try self.emitCoercedExpr(nb, rt) else try self.emitExpr(nb);
                    try self.w.writeAll(";\n");
                }
            } else {
                try self.w.writeAll("unreachable;\n");
            }
        }
        self.indent -= 1;
        try self.writeIndent();
        try self.w.writeAll("}\n");
        self.indent -= 1;
        try self.writeIndent();
        try self.w.writeByte('}');
    }

    fn caseSubjectType(self: *const Emitter, ce: anytype, index: usize) ?*const sema.Ty {
        const ty = self.checked.exprType(ce.subjects[index]) orelse return null;
        if (ty.* == .view and ty.view.target.isInteger() != null and sema.hasIntegerPattern(ce.arms, index)) {
            return ty.view.target;
        }
        return ty;
    }

    fn emitCaseSubject(self: *Emitter, ce: anytype, index: usize) Io.Writer.Error!void {
        const subject = ce.subjects[index];
        if (self.checked.exprType(subject) != self.caseSubjectType(ce, index)) {
            try self.emitIntegerOperand(subject, null);
        } else {
            try self.emitExpr(subject);
        }
    }

    fn emitCaseExpr(self: *Emitter, full_expr: *const ast.Expr, ce: anytype) Io.Writer.Error!void {
        const res_ty = self.checked.exprType(full_expr);
        const res_void = if (res_ty) |rt| isVoidTy(rt) else true;

        if (ce.subjects.len == 1) {
            const sub_ty = self.checked.exprType(ce.subjects[0]);
            if (sub_ty != null and sub_ty.?.* == .option and self.canUseOptionIf(ce)) {
                try self.emitOptionCaseExpr(full_expr, ce, sub_ty.?.option, sub_ty.?);
                return;
            }
        }

        if (self.canUseZigSwitch(ce)) {
            const sub_ty = self.caseSubjectType(ce, 0);
            const compact_adt: ?*const sema.CheckedADT = if (sub_ty != null and sub_ty.?.* == .adt and
                isCompactPackedADT(&self.checked.adts[sub_ty.?.adt]))
                &self.checked.adts[sub_ty.?.adt]
            else
                null;
            const is_result_union = sub_ty != null and sub_ty.?.* == .result;
            const is_adt_union = is_result_union or (if (compact_adt == null and sub_ty != null and sub_ty.?.* == .adt)
                !isPureEnumADT(&self.checked.adts[sub_ty.?.adt])
            else
                false);

            var compact_lbl: usize = 0;
            if (compact_adt != null) {
                compact_lbl = self.nextLabel();
                if (res_void) {
                    try self.w.writeAll("{\n");
                } else {
                    try self.w.print("blk_{d}: {{\n", .{compact_lbl});
                }
                self.indent += 1;
                try self.writeIndent();
                try self.w.print("const __adt_{d} = ", .{compact_lbl});
                try self.emitExpr(ce.subjects[0]);
                try self.w.writeAll(";\n");
                try self.writeIndent();
                if (!res_void) {
                    try self.w.print("break :blk_{d} switch (__adt_{d}.tag) {{\n", .{ compact_lbl, compact_lbl });
                } else {
                    try self.w.print("switch (__adt_{d}.tag) {{\n", .{compact_lbl});
                }
            } else {
                try self.w.writeAll("switch (");
                try self.emitCaseSubject(ce, 0);
                try self.w.writeAll(") {\n");
            }
            self.indent += 1;
            var emitted_else = false;
            for (ce.arms) |arm| {
                try self.writeIndent();
                const pat0 = arm.alternatives[0][0];
                var bind_ident: ?[]const u8 = null;
                var compact_var_ft: ?*const sema.Ty = null;
                var multi_bindings: []const ast.PatternArg = &.{};

                if (arm.alternatives.len == 1 and (pat0.* == .wildcard or pat0.* == .ident)) {
                    emitted_else = true;
                    try self.w.writeAll("else => ");
                    if (pat0.* == .ident) {
                        bind_ident = self.sourceOf(pat0.ident.name);
                        compact_var_ft = sub_ty;
                    }
                } else {
                    for (arm.alternatives, 0..) |row, ri| {
                        if (ri > 0) try self.w.writeAll(", ");
                        try self.emitSwitchPattern(row[0], is_adt_union);
                    }
                    try self.w.writeAll(" => ");
                    if (pat0.* == .constructor and pat0.constructor.args.len > 0) {
                        if (compact_adt) |cadt| {
                            if (pat0.constructor.args.len == 1 and pat0.constructor.args[0].pattern.* == .ident) {
                                const bn = self.sourceOf(pat0.constructor.args[0].pattern.ident.name);
                                const vname = if (pat0.constructor.path.len > 0)
                                    self.sourceOf(pat0.constructor.path[pat0.constructor.path.len - 1])
                                else
                                    "";
                                for (cadt.variants) |v| {
                                    if (std.mem.eql(u8, v.name, vname) and v.field_types.len == 1) {
                                        compact_var_ft = v.field_types[0];
                                        break;
                                    }
                                }
                                bind_ident = bn;
                            }
                        } else if (is_adt_union) {
                            if (pat0.constructor.args.len == 1) {
                                const arg_p = pat0.constructor.args[0].pattern;
                                if (arg_p.* == .ident) {
                                    const bn = self.sourceOf(arg_p.ident.name);
                                    try self.w.writeByte('|');
                                    try self.emitIdent(bn);
                                    try self.w.writeAll("| ");
                                    bind_ident = bn;
                                }
                            } else {
                                var any_bound = false;
                                for (pat0.constructor.args) |pa| {
                                    if (pa.pattern.* == .ident) any_bound = true;
                                }
                                if (any_bound) {
                                    try self.w.writeAll("|__tup_cap| ");
                                    multi_bindings = pat0.constructor.args;
                                }
                            }
                        }
                    }
                }

                if (bind_ident != null or multi_bindings.len > 0) {
                    const need_cap_block = (compact_adt != null and bind_ident != null) or
                        (bind_ident != null and !self.exprMentionsIdent(arm.body, bind_ident.?)) or
                        multi_bindings.len > 0;
                    if (!need_cap_block and bind_ident != null) {
                        const arm_sv = self.pushScopeVars();
                        defer self.popScopeVars(arm_sv);
                        if (is_result_union and pat0.* == .constructor) {
                            const vn = if (pat0.constructor.path.len > 0)
                                self.sourceOf(pat0.constructor.path[pat0.constructor.path.len - 1])
                            else
                                "";
                            const payload_ty: ?*const sema.Ty = if (std.mem.eql(u8, vn, "Ok"))
                                sub_ty.?.result.ok
                            else if (std.mem.eql(u8, vn, "Err"))
                                sub_ty.?.result.err
                            else
                                null;
                            self.bindScopeVar(bind_ident.?, payload_ty, false);
                        } else if (is_adt_union and pat0.* == .constructor) {
                            // Capture binding already bound in Zig arm.
                            self.bindScopeVar(bind_ident.?, null, false);
                        } else if (sub_ty) |st| {
                            self.bindScopeVar(bind_ident.?, st, false);
                        }
                        if (res_void) {
                            if (self.isVoidExpr(arm.body)) {
                                try self.emitExpr(arm.body);
                            } else {
                                try self.w.writeAll("{ _ = ");
                                try self.emitExpr(arm.body);
                                try self.w.writeAll("; }");
                            }
                        } else if (res_ty) |rt| {
                            try self.emitCoercedExpr(arm.body, rt);
                        } else {
                            try self.emitExpr(arm.body);
                        }
                        try self.w.writeAll(",\n");
                        continue;
                    }
                    const lbl = self.nextLabel();
                    const arm_sv = self.pushScopeVars();
                    defer self.popScopeVars(arm_sv);
                    if (res_void) {
                        try self.w.writeAll("{\n");
                    } else {
                        try self.w.print("blk_{d}: {{\n", .{lbl});
                    }
                    self.indent += 1;
                    if (compact_adt) |cadt| {
                        if (bind_ident) |bn| {
                            try self.writeIndent();
                            try self.w.writeAll("const ");
                            try self.emitIdent(bn);
                            if (pat0.* == .ident) {
                                try self.w.print(" = __adt_{d};\n", .{compact_lbl});
                                self.bindScopeVar(bn, compact_var_ft, false);
                            } else if (compact_var_ft) |vft| {
                                try self.w.writeAll(": ");
                                try self.emitTy(vft);
                                try self.w.writeAll(" = ");
                                try self.emitUnpackCompactPayload(compact_lbl, vft, cadt.adt_layout.max_payload_bits);
                                try self.w.writeAll(";\n");
                                self.bindScopeVar(bn, vft, false);
                            } else {
                                try self.w.print(" = __adt_{d}.payload;\n", .{compact_lbl});
                            }
                            if (!self.exprMentionsIdent(arm.body, bn)) {
                                try self.writeIndent();
                                try self.w.writeAll("_ = ");
                                try self.emitIdent(bn);
                                try self.w.writeAll(";\n");
                            }
                        }
                    } else if (bind_ident) |bn| {
                        self.bindScopeVar(bn, null, false);
                        if (!self.exprMentionsIdent(arm.body, bn)) {
                            try self.writeIndent();
                            try self.w.writeAll("_ = ");
                            try self.emitIdent(bn);
                            try self.w.writeAll(";\n");
                        }
                    }
                    for (multi_bindings, 0..) |pa, pi| {
                        if (pa.pattern.* == .ident) {
                            const vn = self.sourceOf(pa.pattern.ident.name);
                            try self.writeIndent();
                            try self.w.writeAll("const ");
                            try self.emitIdent(vn);
                            try self.w.print(" = __tup_cap[{d}];\n", .{pi});
                            self.bindScopeVar(vn, null, false);
                            if (!self.exprMentionsIdent(arm.body, vn)) {
                                try self.writeIndent();
                                try self.w.writeAll("_ = ");
                                try self.emitIdent(vn);
                                try self.w.writeAll(";\n");
                            }
                        }
                    }
                    try self.writeIndent();
                    if (res_void) {
                        if (self.isVoidExpr(arm.body)) {
                            try self.emitExpr(arm.body);
                            try self.w.writeAll(";\n");
                        } else {
                            try self.w.writeAll("_ = ");
                            try self.emitExpr(arm.body);
                            try self.w.writeAll(";\n");
                        }
                    } else {
                        try self.w.print("break :blk_{d} ", .{lbl});
                        if (res_ty) |rt| try self.emitCoercedExpr(arm.body, rt) else try self.emitExpr(arm.body);
                        try self.w.writeAll(";\n");
                    }
                    self.indent -= 1;
                    try self.writeIndent();
                    try self.w.writeAll("},\n");
                } else {
                    if (res_void) {
                        if (self.isVoidExpr(arm.body)) {
                            try self.emitExpr(arm.body);
                        } else {
                            try self.w.writeAll("{ _ = ");
                            try self.emitExpr(arm.body);
                            try self.w.writeAll("; }");
                        }
                    } else if (res_ty) |rt| {
                        try self.emitCoercedExpr(arm.body, rt);
                    } else {
                        try self.emitExpr(arm.body);
                    }
                    try self.w.writeAll(",\n");
                }
            }
            if (!emitted_else and (sub_ty == null or
                (sub_ty.?.* != .adt and sub_ty.?.* != .bool and sub_ty.?.* != .result and !self.zigIntSwitchComplete(sub_ty.?, ce.arms))))
            {
                try self.writeIndent();
                try self.w.writeAll("else => unreachable,\n");
            }
            self.indent -= 1;
            try self.writeIndent();
            if (compact_adt != null) {
                if (!res_void) {
                    try self.w.writeAll("};\n");
                } else {
                    try self.w.writeAll("}\n");
                }
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeByte('}');
            } else {
                try self.w.writeByte('}');
            }
            return;
        }

        // General multi-subject / guarded `case` lowered to labeled `if / else if / else`.
        const lbl = self.nextLabel();
        try self.w.print("blk_{d}: {{\n", .{lbl});
        self.indent += 1;
        for (ce.subjects, 0..) |_, si| {
            try self.writeIndent();
            try self.w.print("const __subj_{d} = ", .{si});
            try self.emitCaseSubject(ce, si);
            try self.w.writeAll(";\n");
            try self.writeIndent();
            try self.w.print("_ = __subj_{d};\n", .{si});
        }
        for (ce.arms, 0..) |arm, ai| {
            const row0: []const *const ast.Pattern = if (arm.alternatives.len > 0) arm.alternatives[0] else &.{};
            try self.writeIndent();
            if (ai == 0) {
                try self.w.writeAll("if (");
            } else {
                try self.w.writeAll("else if (");
            }
            var wrote_cond = false;
            if (arm.alternatives.len > 0) {
                try self.w.writeByte('(');
                for (arm.alternatives, 0..) |row, ri| {
                    if (ri > 0) try self.w.writeAll(" or ");
                    try self.w.writeByte('(');
                    var any_in_row = false;
                    for (row, 0..) |pat, pi| {
                        if (pi > 0) try self.w.writeAll(" and ");
                        try self.emitFallbackPatCond(pi, pat);
                        any_in_row = true;
                    }
                    if (!any_in_row) try self.w.writeAll("true");
                    try self.w.writeByte(')');
                }
                try self.w.writeByte(')');
                wrote_cond = true;
            }
            if (!wrote_cond) try self.w.writeAll("true");
            try self.w.writeAll(") {\n");
            self.indent += 1;
            for (row0, 0..) |pat, pi| {
                if (pat.* == .ident) {
                    const bn = self.sourceOf(pat.ident.name);
                    try self.writeIndent();
                    try self.w.writeAll("const ");
                    try self.emitIdent(bn);
                    try self.w.print(" = __subj_{d};\n", .{pi});
                    if (!self.exprMentionsIdent(arm.body, bn) and !(arm.guard != null and self.exprMentionsIdent(arm.guard.?, bn))) {
                        try self.writeIndent();
                        try self.w.writeAll("_ = ");
                        try self.emitIdent(bn);
                        try self.w.writeAll(";\n");
                    }
                }
            }
            if (arm.guard) |g| {
                try self.writeIndent();
                try self.w.writeAll("if (");
                try self.emitExpr(g);
                try self.w.writeAll(") {\n");
                self.indent += 1;
            }
            try self.writeIndent();
            if (res_void) {
                if (self.isVoidExpr(arm.body)) {
                    try self.emitExpr(arm.body);
                    try self.w.writeAll(";\n");
                } else {
                    try self.w.writeAll("_ = ");
                    try self.emitExpr(arm.body);
                    try self.w.writeAll(";\n");
                }
                try self.writeIndent();
                try self.w.print("break :blk_{d};\n", .{lbl});
            } else {
                try self.w.print("break :blk_{d} ", .{lbl});
                if (res_ty) |rt| try self.emitCoercedExpr(arm.body, rt) else try self.emitExpr(arm.body);
                try self.w.writeAll(";\n");
            }
            if (arm.guard != null) {
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("}\n");
            }
            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeAll("}\n");
        }
        try self.writeIndent();
        if (res_void) {
            try self.w.print("break :blk_{d};\n", .{lbl});
        } else {
            try self.w.writeAll("unreachable;\n");
        }
        self.indent -= 1;
        try self.writeIndent();
        try self.w.writeByte('}');
    }

    fn emitFallbackPatCond(self: *Emitter, subj_idx: usize, pat: *const ast.Pattern) Io.Writer.Error!void {
        switch (pat.*) {
            .wildcard, .ident => try self.w.writeAll("true"),
            .literal => |lit| {
                if (lit.tok.tag == .string_literal) {
                    try self.w.print("std.mem.eql(u8, __subj_{d}, ", .{subj_idx});
                    try self.emitStringLit(ast.Span.fromLoc(lit.tok.loc));
                    try self.w.writeByte(')');
                } else {
                    try self.w.print("(__subj_{d} == ", .{subj_idx});
                    try self.emitSwitchPattern(pat, false);
                    try self.w.writeByte(')');
                }
            },
            .range => |rg| {
                try self.w.print("(__subj_{d} >= ", .{subj_idx});
                try self.emitSwitchPattern(rg.lo, false);
                try self.w.print(" and __subj_{d} {s} ", .{ subj_idx, if (rg.inclusive) "<=" else "<" });
                try self.emitSwitchPattern(rg.hi, false);
                try self.w.writeByte(')');
            },
            .constructor => |c| {
                const vname = if (c.path.len > 0) self.sourceOf(c.path[c.path.len - 1]) else "";
                if (std.mem.eql(u8, vname, "None")) {
                    try self.w.print("(__subj_{d} == null)", .{subj_idx});
                } else if (std.mem.eql(u8, vname, "Some")) {
                    try self.w.print("(__subj_{d} != null)", .{subj_idx});
                } else {
                    try self.w.print("(__subj_{d} == .{s})", .{ subj_idx, vname });
                }
            },
            .or_pat => |op| {
                try self.w.writeByte('(');
                for (op.alternatives, 0..) |alt, ai| {
                    if (ai > 0) try self.w.writeAll(" or ");
                    try self.emitFallbackPatCond(subj_idx, alt);
                }
                try self.w.writeByte(')');
            },
            else => try self.w.writeAll("true"),
        }
    }

    fn emitSwitchPattern(self: *Emitter, pat: *const ast.Pattern, is_adt_union: bool) Io.Writer.Error!void {
        _ = is_adt_union;
        switch (pat.*) {
            .literal => |lit| {
                if (lit.negative) try self.w.writeByte('-');
                const s = self.sourceOf(ast.Span.fromLoc(lit.tok.loc));
                if (lit.tok.tag == .int_literal) {
                    const p = int_range.parseIntLiteral(s) orelse {
                        try self.w.writeAll(s);
                        return;
                    };
                    try self.w.print("{d}", .{p.value});
                } else {
                    try self.w.writeAll(s);
                }
            },
            .range => |rg| {
                try self.emitSwitchPattern(rg.lo, false);
                try self.w.writeAll("...");
                try self.emitSwitchPattern(rg.hi, false);
            },
            .constructor => |c| {
                const vname = if (c.path.len > 0) self.sourceOf(c.path[c.path.len - 1]) else "_";
                try self.w.writeByte('.');
                try self.emitIdent(vname);
            },
            .or_pat => |op| {
                for (op.alternatives, 0..) |alt, i| {
                    if (i > 0) try self.w.writeAll(", ");
                    try self.emitSwitchPattern(alt, false);
                }
            },
            .wildcard, .ident => try self.w.writeAll("else"),
            else => try self.w.writeAll("else"),
        }
    }

    fn rootIdentOf(self: *const Emitter, expr: *const ast.Expr) ?[]const u8 {
        var cur = expr;
        while (true) {
            switch (cur.*) {
                .ident => |sp| return self.sourceOf(sp),
                .field => |f| cur = f.target,
                .index => |ix| cur = ix.target,
                else => return null,
            }
        }
    }

    fn blockMentionsIdent(self: *const Emitter, blk: *const ast.Block, name: []const u8) bool {
        return self.stmtsMentionIdent(blk.stmts, blk.tail, name);
    }

    fn stmtsMentionIdent(self: *const Emitter, stmts: []const ast.Stmt, tail: ?*const ast.Expr, name: []const u8) bool {
        for (stmts) |*st| {
            if (self.stmtMentionsIdent(st, name)) return true;
        }
        if (tail) |t| {
            if (self.exprMentionsIdent(t, name)) return true;
        }
        return false;
    }

    fn stmtMentionsIdent(self: *const Emitter, stmt: *const ast.Stmt, name: []const u8) bool {
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

    fn exprMentionsIdent(self: *const Emitter, expr: *const ast.Expr, name: []const u8) bool {
        return switch (expr.*) {
            .ident => |sp| std.mem.eql(u8, self.sourceOf(sp), name),
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
                    } else if (std.mem.eql(u8, self.sourceOf(rf.name), name)) {
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
            .using_expr => |ue| self.exprMentionsIdent(ue.target, name),
            .todo_expr => |td| if (td.message) |m| self.exprMentionsIdent(m, name) else false,
            .panic_expr => |pn| if (pn.message) |m| self.exprMentionsIdent(m, name) else false,
            else => false,
        };
    }

    fn blockMutatesOrBorrowsIdent(self: *const Emitter, blk: *const ast.Block, name: []const u8) bool {
        return self.stmtsMutateOrBorrowIdent(blk.stmts, blk.tail, name);
    }

    fn stmtsMutateOrBorrowIdent(self: *const Emitter, stmts: []const ast.Stmt, tail: ?*const ast.Expr, name: []const u8) bool {
        for (stmts) |*st| {
            if (self.stmtMutatesOrBorrowsIdent(st, name)) return true;
        }
        if (tail) |t| {
            if (self.exprMutatesOrBorrowsIdent(t, name)) return true;
        }
        return false;
    }

    fn stmtMutatesOrBorrowsIdent(self: *const Emitter, stmt: *const ast.Stmt, name: []const u8) bool {
        return switch (stmt.*) {
            .let_stmt => |ls| self.exprMutatesOrBorrowsIdent(ls.value, name),
            .use_stmt => |us| self.exprMutatesOrBorrowsIdent(us.expr, name),
            .assign_stmt => |asg| blk: {
                if (self.rootIdentOf(asg.target)) |rn| {
                    if (std.mem.eql(u8, rn, name)) break :blk true;
                }
                break :blk self.exprMutatesOrBorrowsIdent(asg.value, name);
            },
            .return_stmt => |rs| if (rs.value) |v| self.exprMutatesOrBorrowsIdent(v, name) else false,
            .while_stmt => |ws| self.exprMutatesOrBorrowsIdent(ws.cond, name) or self.blockMutatesOrBorrowsIdent(&ws.body, name),
            .for_stmt => |fs| self.exprMutatesOrBorrowsIdent(fs.iter, name) or self.blockMutatesOrBorrowsIdent(&fs.body, name),
            .expr_stmt => |es| self.exprMutatesOrBorrowsIdent(es.expr, name),
        };
    }

    fn isMutatingStdIntrinsic(kind: sema.StdIntrinsicKind) bool {
        return switch (kind) {
            .vec_push,
            .vec_pop,
            .vec_set,
            .vec_swap_remove,
            .vec_reserve,
            .vec_clear,
            .map_insert,
            .map_put,
            .map_remove,
            .map_clear,
            .set_insert,
            .set_remove,
            .set_clear,
            .deque_push_back,
            .deque_push_front,
            .deque_pop_front,
            .deque_pop_back,
            .deque_clear,
            => true,
            else => false,
        };
    }

    fn stmtsMayMoveIdent(self: *const Emitter, stmts: []const ast.Stmt, tail: ?*const ast.Expr, name: []const u8) bool {
        for (stmts) |*st| {
            if (self.stmtMayMoveIdent(st, name)) return true;
        }
        if (tail) |t| {
            if (self.exprIsDirectMoveOf(t, name) or self.exprMayMoveIdent(t, name)) return true;
        }
        return false;
    }

    fn blockMayMoveIdent(self: *const Emitter, blk: *const ast.Block, name: []const u8) bool {
        return self.stmtsMayMoveIdent(blk.stmts, blk.tail, name);
    }

    fn exprIsDirectMoveOf(self: *const Emitter, expr: *const ast.Expr, name: []const u8) bool {
        return switch (expr.*) {
            .ident => |sp| std.mem.eql(u8, self.sourceOf(sp), name),
            .block => |*b| if (b.tail) |t| self.exprIsDirectMoveOf(t, name) else false,
            .if_expr => |ie| (if (ie.then_block.tail) |tt| self.exprIsDirectMoveOf(tt, name) else false) or
                (if (ie.else_branch) |eb| self.exprIsDirectMoveOf(eb, name) else false),
            else => false,
        };
    }

    fn exprIsDirectMoveAnyOwned(self: *const Emitter, expr: *const ast.Expr) bool {
        return switch (expr.*) {
            .ident => |sp| blk: {
                if (self.lookupScopeVar(self.sourceOf(sp))) |sv| {
                    break :blk sv.is_owned_dyn and sv.has_moved_flag;
                }
                break :blk false;
            },
            .block => |*b| if (b.tail) |t| self.exprIsDirectMoveAnyOwned(t) else false,
            .if_expr => |ie| (if (ie.then_block.tail) |tt| self.exprIsDirectMoveAnyOwned(tt) else false) or
                (if (ie.else_branch) |eb| self.exprIsDirectMoveAnyOwned(eb) else false),
            else => false,
        };
    }

    fn stmtMayMoveIdent(self: *const Emitter, stmt: *const ast.Stmt, name: []const u8) bool {
        return switch (stmt.*) {
            .let_stmt => |ls| self.exprIsDirectMoveOf(ls.value, name) or self.exprMayMoveIdent(ls.value, name),
            .use_stmt => |us| self.exprMayMoveIdent(us.expr, name),
            .assign_stmt => |asg| self.exprIsDirectMoveOf(asg.value, name) or self.exprMayMoveIdent(asg.value, name),
            .return_stmt => |rs| if (rs.value) |v| self.exprIsDirectMoveOf(v, name) or self.exprMayMoveIdent(v, name) else false,
            .while_stmt => |ws| self.exprMayMoveIdent(ws.cond, name) or self.blockMayMoveIdent(&ws.body, name),
            .for_stmt => |fs| self.exprMayMoveIdent(fs.iter, name) or self.blockMayMoveIdent(&fs.body, name),
            .expr_stmt => |es| self.exprIsDirectMoveOf(es.expr, name) or self.exprMayMoveIdent(es.expr, name),
        };
    }

    fn callArgConsumesByValue(self: *const Emitter, call_expr: *const ast.Expr, callee: *const ast.Expr, idx: usize, piped: bool) bool {
        if (self.checked.std_intrinsic_calls.get(call_expr)) |_| {
            return idx > 0 or (piped and idx == 0);
        }
        const cn_opt = self.checked.resolvedCallName(callee) orelse
            if (callee.* == .ident) self.sourceOf(callee.ident) else null;
        if (cn_opt) |cn| {
            if (self.findCheckedFn(cn)) |cf| {
                if (idx < cf.param_types.len) {
                    const pt = cf.param_types[idx];
                    return !isPointerType(pt) and isOwnedDynamicTy(pt);
                }
            }
        }
        if (callee.* == .upper_ident) {
            const un = self.sourceOf(callee.upper_ident);
            if (std.mem.eql(u8, un, "Some") or std.mem.eql(u8, un, "Ok") or std.mem.eql(u8, un, "Err")) return true;
        }
        return false;
    }

    fn exprMayMoveIdent(self: *const Emitter, expr: *const ast.Expr, name: []const u8) bool {
        return switch (expr.*) {
            .unary => |u| self.exprMayMoveIdent(u.operand, name),
            .binary => |b| blk: {
                if (b.op == .pipe and b.right.* == .call) {
                    if (self.checked.std_intrinsic_calls.get(b.right) == null and
                        self.callArgConsumesByValue(b.right, b.right.call.callee, 0, false) and
                        self.exprIsDirectMoveOf(b.left, name))
                    {
                        break :blk true;
                    }
                    if (b.right.call.callee.* == .ident and
                        std.mem.eql(u8, self.sourceOf(b.right.call.callee.ident), "map_in_place") and
                        self.exprIsDirectMoveOf(b.left, name) and
                        isOwnedDynamicTy(self.checked.exprType(b.left)))
                    {
                        // Non-fold pipe returning Vec moves base through __raw unless discarded;
                        // check only when consumed as value (handled by parent), so inspect args only.
                    }
                }
                break :blk self.exprMayMoveIdent(b.left, name) or self.exprMayMoveIdent(b.right, name);
            },
            .call => |c| blk: {
                const is_intr = self.checked.std_intrinsic_calls.get(expr) != null;
                for (c.args, 0..) |a, ai| {
                    if (is_intr and ai == 0) {
                        if (self.exprMayMoveIdent(a.value, name)) break :blk true;
                        continue;
                    }
                    if (self.callArgConsumesByValue(expr, c.callee, ai, false) and self.exprIsDirectMoveOf(a.value, name)) {
                        break :blk true;
                    }
                    if (self.exprMayMoveIdent(a.value, name)) break :blk true;
                }
                break :blk false;
            },
            .record_lit => |rl| blk: {
                for (rl.fields) |rf| {
                    if (rf.value) |v| {
                        if (self.exprIsDirectMoveOf(v, name) or self.exprMayMoveIdent(v, name)) break :blk true;
                    } else if (std.mem.eql(u8, self.sourceOf(rf.name), name)) {
                        break :blk true;
                    }
                }
                break :blk false;
            },
            .tuple => |tp| blk: {
                for (tp.elems) |el| if (self.exprIsDirectMoveOf(el, name) or self.exprMayMoveIdent(el, name)) break :blk true;
                break :blk false;
            },
            .list => |ls| blk: {
                for (ls.elems) |el| if (self.exprIsDirectMoveOf(el, name) or self.exprMayMoveIdent(el, name)) break :blk true;
                break :blk false;
            },
            .block => |*blk| self.blockMayMoveIdent(blk, name),
            .if_expr => |ie| self.exprMayMoveIdent(ie.cond, name) or
                self.blockMayMoveIdent(&ie.then_block, name) or
                (if (ie.else_branch) |eb| self.exprMayMoveIdent(eb, name) else false),
            .case_expr => |ce| blk: {
                for (ce.arms) |arm| if (self.exprMayMoveIdent(arm.body, name)) break :blk true;
                break :blk false;
            },
            else => false,
        };
    }

    fn exprMutatesOrBorrowsIdent(self: *const Emitter, expr: *const ast.Expr, name: []const u8) bool {
        return switch (expr.*) {
            .unary => |u| (u.op == .addr_of and blk: {
                const rn = self.rootIdentOf(u.operand) orelse break :blk false;
                break :blk std.mem.eql(u8, rn, name);
            }) or self.exprMutatesOrBorrowsIdent(u.operand, name),
            .binary => |b| blk: {
                if (b.op == .pipe and b.right.* == .call) {
                    if (self.checked.std_intrinsic_calls.get(b.right)) |intr| {
                        if (isMutatingStdIntrinsic(intr.kind)) {
                            if (self.rootIdentOf(b.left)) |rn| {
                                if (std.mem.eql(u8, rn, name)) break :blk true;
                            }
                        }
                    } else {
                        if (b.right.call.callee.* == .ident and
                            std.mem.eql(u8, self.sourceOf(b.right.call.callee.ident), "map_in_place"))
                        {
                            if (self.rootIdentOf(b.left)) |rn| {
                                if (std.mem.eql(u8, rn, name)) break :blk true;
                            }
                        }
                        const cn_opt = self.checked.resolvedCallName(b.right.call.callee) orelse
                            if (b.right.call.callee.* == .ident) self.sourceOf(b.right.call.callee.ident) else null;
                        if (cn_opt) |cn| {
                            if (self.findCheckedFn(cn)) |cf| {
                                if (cf.param_types.len > 0 and isPointerType(cf.param_types[0])) {
                                    if (self.rootIdentOf(b.left)) |rn| {
                                        if (std.mem.eql(u8, rn, name)) break :blk true;
                                    }
                                }
                            }
                        }
                    }
                }
                break :blk self.exprMutatesOrBorrowsIdent(b.left, name) or self.exprMutatesOrBorrowsIdent(b.right, name);
            },
            .call => |c| blk: {
                if (self.checked.std_intrinsic_calls.get(expr)) |intr| {
                    if (isMutatingStdIntrinsic(intr.kind) and c.args.len > 0) {
                        if (self.rootIdentOf(c.args[0].value)) |rn| {
                            if (std.mem.eql(u8, rn, name)) break :blk true;
                        }
                    }
                } else {
                    const cn_opt = self.checked.resolvedCallName(c.callee) orelse
                        if (c.callee.* == .ident) self.sourceOf(c.callee.ident) else null;
                    if (cn_opt) |cn| {
                        if (self.findCheckedFn(cn)) |cf| {
                            for (c.args, 0..) |a, ai| {
                                if (ai < cf.param_types.len and isPointerType(cf.param_types[ai])) {
                                    if (self.rootIdentOf(a.value)) |rn| {
                                        if (std.mem.eql(u8, rn, name)) break :blk true;
                                    }
                                }
                            }
                        }
                    }
                }
                for (c.args) |a| {
                    if (self.exprMutatesOrBorrowsIdent(a.value, name)) break :blk true;
                }
                break :blk false;
            },
            .block => |*blk| self.blockMutatesOrBorrowsIdent(blk, name),
            .if_expr => |ie| self.exprMutatesOrBorrowsIdent(ie.cond, name) or
                self.blockMutatesOrBorrowsIdent(&ie.then_block, name) or
                (if (ie.else_branch) |eb| self.exprMutatesOrBorrowsIdent(eb, name) else false),
            .case_expr => |ce| blk: {
                for (ce.arms) |arm| {
                    if (self.exprMutatesOrBorrowsIdent(arm.body, name)) break :blk true;
                }
                break :blk false;
            },
            .view_expr => |vw| blk: {
                if (vw.mode != .shared) {
                    if (self.rootIdentOf(vw.target)) |rn| {
                        if (std.mem.eql(u8, rn, name)) break :blk true;
                    }
                }
                break :blk self.blockMutatesOrBorrowsIdent(&vw.body, name);
            },
            .fork_expr => |fk| blk: {
                for (fk.branches) |*br| if (self.blockMutatesOrBorrowsIdent(br, name)) break :blk true;
                break :blk false;
            },
            .using_expr => |ue| self.exprMutatesOrBorrowsIdent(ue.target, name),
            else => false,
        };
    }

    const ForkCapture = struct {
        name: []const u8,
        ty: *const sema.Ty,
        by_ptr: bool,
    };

    const SimdFieldEntry = struct {
        fidx: usize,
        name: []const u8,
        ty: *const sema.Ty,
        read: bool,
        written: bool,
    };

    const SimdLocalVar = struct {
        name: []const u8,
        ty: *const sema.Ty,
    };

    fn isSimdPrimitiveTy(ty: *const sema.Ty) ?sema.Ty {
        return switch (ty.*) {
            .f32 => .f32,
            .f64 => .f64,
            .int => |it| if (it.bits == 8 or it.bits == 16 or it.bits == 32 or it.bits == 64) ty.* else null,
            .int_range => |ir| if (ir.synthesized.bits == 8 or ir.synthesized.bits == 16 or ir.synthesized.bits == 32 or ir.synthesized.bits == 64)
                .{ .int = ir.synthesized }
            else
                null,
            else => null,
        };
    }

    fn eqSimdScalarTy(a: *const sema.Ty, b: *const sema.Ty) bool {
        const pa = isSimdPrimitiveTy(a) orelse return false;
        const pb = isSimdPrimitiveTy(b) orelse return false;
        return switch (pa) {
            .f32 => pb == .f32,
            .f64 => pb == .f64,
            .int => |ia| switch (pb) {
                .int => |ib| ia.signed == ib.signed and ia.bits == ib.bits,
                else => false,
            },
            else => false,
        };
    }

    fn findOrAddSimdField(
        self: *Emitter,
        entries: *std.ArrayList(SimdFieldEntry),
        rec: *const sema.CheckedRecord,
        fname: []const u8,
    ) ?usize {
        const fidx = findRecordFieldIdx(rec, fname) orelse return null;
        if (fieldBinByte(rec, fidx) != null) return null;
        const fty = rec.fields[fidx].ty;
        if (isSimdPrimitiveTy(fty) == null) return null;
        for (entries.items, 0..) |e, idx| {
            if (e.fidx == fidx) return idx;
        }
        entries.append(self.alloc, .{
            .fidx = fidx,
            .name = rec.fields[fidx].name,
            .ty = fty,
            .read = false,
            .written = false,
        }) catch return null;
        return entries.items.len - 1;
    }

    fn inferSimdExprScalarTy(
        self: *const Emitter,
        rec: *const sema.CheckedRecord,
        locals: []const SimdLocalVar,
        expr: *const ast.Expr,
    ) ?*const sema.Ty {
        return switch (expr.*) {
            .field => |fld| blk: {
                if (fld.target.* == .ident and fld.target.ident.slice(self.tree.source).len > 0) {
                    const fname = self.sourceOf(fld.name);
                    if (findRecordFieldIdx(rec, fname)) |fi| {
                        const fty = rec.fields[fi].ty;
                        if (isSimdPrimitiveTy(fty) != null) break :blk fty;
                    }
                }
                break :blk null;
            },
            .ident => |sp| blk: {
                const name = self.sourceOf(sp);
                for (locals) |lv| {
                    if (std.mem.eql(u8, lv.name, name)) break :blk lv.ty;
                }
                if (self.checked.exprType(expr)) |ety| {
                    if (isSimdPrimitiveTy(ety) != null) break :blk ety;
                }
                if (self.lookupScopeVar(name)) |sv| {
                    if (sv.ty != null and isSimdPrimitiveTy(sv.ty.?) != null) break :blk sv.ty.?;
                }
                break :blk null;
            },
            .cast => |c| if (self.checked.exprType(expr)) |ety| (if (isSimdPrimitiveTy(ety) != null) ety else null) else self.inferSimdExprScalarTy(rec, locals, c.expr),
            .unary => |u| self.inferSimdExprScalarTy(rec, locals, u.operand),
            .binary => |b| self.inferSimdExprScalarTy(rec, locals, b.left) orelse self.inferSimdExprScalarTy(rec, locals, b.right),
            .if_expr => |ie| (if (ie.then_block.tail) |t| self.inferSimdExprScalarTy(rec, locals, t) else null) orelse
                (if (ie.else_branch) |eb| (if (eb.* == .block and eb.block.tail != null) self.inferSimdExprScalarTy(rec, locals, eb.block.tail.?) else null) else null),
            else => if (self.checked.exprType(expr)) |ety| (if (isSimdPrimitiveTy(ety) != null) ety else null) else null,
        };
    }

    fn isSimdCmpOp(op: ast.BinaryOp) bool {
        return switch (op) {
            .eq, .ne, .lt, .le, .gt, .ge => true,
            else => false,
        };
    }

    fn isValidSimdCmpExpr(
        self: *Emitter,
        rec: *const sema.CheckedRecord,
        elem_param: []const u8,
        locals: []const SimdLocalVar,
        entries: *std.ArrayList(SimdFieldEntry),
        cond: *const ast.Expr,
    ) ?*const sema.Ty {
        if (cond.* != .binary) return null;
        const b = cond.binary;
        if (!isSimdCmpOp(b.op)) return null;
        const cmp_ty = self.inferSimdExprScalarTy(rec, locals, b.left) orelse
            self.inferSimdExprScalarTy(rec, locals, b.right) orelse return null;
        if (!self.isValidSimdExprForTy(rec, elem_param, locals, entries, b.left, cmp_ty)) return null;
        if (!self.isValidSimdExprForTy(rec, elem_param, locals, entries, b.right, cmp_ty)) return null;
        return cmp_ty;
    }

    fn isValidSimdExprForTy(
        self: *Emitter,
        rec: *const sema.CheckedRecord,
        elem_param: []const u8,
        locals: []const SimdLocalVar,
        entries: *std.ArrayList(SimdFieldEntry),
        expr: *const ast.Expr,
        target_ty: *const sema.Ty,
    ) bool {
        switch (expr.*) {
            .int_lit => return target_ty.isInteger() != null,
            .float_lit => return target_ty.* == .f32 or target_ty.* == .f64,
            .ident => |sp| {
                const name = self.sourceOf(sp);
                if (std.mem.eql(u8, name, elem_param)) return false;
                for (locals) |lv| {
                    if (std.mem.eql(u8, lv.name, name)) return eqSimdScalarTy(lv.ty, target_ty);
                }
                const ety = self.checked.exprType(expr) orelse blk: {
                    const sv = self.lookupScopeVar(name) orelse return false;
                    break :blk sv.ty orelse return false;
                };
                return eqSimdScalarTy(ety, target_ty);
            },
            .field => |fld| {
                if (fld.target.* != .ident) return false;
                if (!std.mem.eql(u8, self.sourceOf(fld.target.ident), elem_param)) return false;
                const fname = self.sourceOf(fld.name);
                const idx = self.findOrAddSimdField(entries, rec, fname) orelse return false;
                if (!eqSimdScalarTy(entries.items[idx].ty, target_ty)) return false;
                entries.items[idx].read = true;
                return true;
            },
            .unary => |u| return u.op == .neg and
                self.isValidSimdExprForTy(rec, elem_param, locals, entries, u.operand, target_ty),
            .binary => |b| return switch (b.op) {
                .add, .sub, .mul, .div => self.isValidSimdExprForTy(rec, elem_param, locals, entries, b.left, target_ty) and
                    self.isValidSimdExprForTy(rec, elem_param, locals, entries, b.right, target_ty),
                .add_wrap, .sub_wrap, .mul_wrap => target_ty.isInteger() != null and
                    self.isValidSimdExprForTy(rec, elem_param, locals, entries, b.left, target_ty) and
                    self.isValidSimdExprForTy(rec, elem_param, locals, entries, b.right, target_ty),
                else => false,
            },
            .cast => |c| {
                const tit = target_ty.isInteger() orelse return false;
                const src_ty = self.inferSimdExprScalarTy(rec, locals, c.expr) orelse return false;
                const sit = src_ty.isInteger() orelse return false;
                if (sit.bits > tit.bits or sit.signed != tit.signed) return false;
                return self.isValidSimdExprForTy(rec, elem_param, locals, entries, c.expr, src_ty);
            },
            .if_expr => |ie| {
                const eb = ie.else_branch orelse return false;
                if (eb.* != .block) return false;
                if (ie.then_block.stmts.len != 0 or ie.then_block.tail == null) return false;
                if (eb.block.stmts.len != 0 or eb.block.tail == null) return false;
                if (self.isValidSimdCmpExpr(rec, elem_param, locals, entries, ie.cond) == null) return false;
                return self.isValidSimdExprForTy(rec, elem_param, locals, entries, ie.then_block.tail.?, target_ty) and
                    self.isValidSimdExprForTy(rec, elem_param, locals, entries, eb.block.tail.?, target_ty);
            },
            else => return false,
        }
    }

    fn collectSimdLambda(
        self: *Emitter,
        rec: *const sema.CheckedRecord,
        elem_param: []const u8,
        body: *const ast.Block,
    ) ?[]SimdFieldEntry {
        if (body.tail != null or body.stmts.len == 0) return null;
        var entries: std.ArrayList(SimdFieldEntry) = .empty;
        var locals: std.ArrayList(SimdLocalVar) = .empty;
        var any_field_write = false;

        for (body.stmts) |st| {
            switch (st) {
                .let_stmt => |ls| {
                    if (ls.pattern.* != .ident) return null;
                    const lname = self.sourceOf(ls.pattern.ident.name);
                    const lty = self.checked.letType(ls.span.start) orelse self.checked.exprType(ls.value) orelse return null;
                    if (isSimdPrimitiveTy(lty) == null) return null;
                    if (!self.isValidSimdExprForTy(rec, elem_param, locals.items, &entries, ls.value, lty)) return null;
                    locals.append(self.alloc, .{ .name = lname, .ty = lty }) catch return null;
                },
                .assign_stmt => |asg| {
                    switch (asg.op) {
                        .assign, .add_assign, .sub_assign, .mul_assign, .div_assign => {},
                        else => return null,
                    }
                    if (asg.target.* == .field) {
                        const fld = asg.target.field;
                        if (fld.target.* != .ident) return null;
                        if (!std.mem.eql(u8, self.sourceOf(fld.target.ident), elem_param)) return null;
                        const fname = self.sourceOf(fld.name);
                        const idx = self.findOrAddSimdField(&entries, rec, fname) orelse return null;
                        const lhs_ty = entries.items[idx].ty;
                        if (asg.op != .assign) entries.items[idx].read = true;
                        entries.items[idx].written = true;
                        any_field_write = true;
                        if (!self.isValidSimdExprForTy(rec, elem_param, locals.items, &entries, asg.value, lhs_ty)) return null;
                    } else if (asg.target.* == .ident) {
                        const tname = self.sourceOf(asg.target.ident);
                        var l_ty: ?*const sema.Ty = null;
                        for (locals.items) |lv| {
                            if (std.mem.eql(u8, lv.name, tname)) {
                                l_ty = lv.ty;
                                break;
                            }
                        }
                        const lhs_ty = l_ty orelse return null;
                        if (!self.isValidSimdExprForTy(rec, elem_param, locals.items, &entries, asg.value, lhs_ty)) return null;
                    } else {
                        return null;
                    }
                },
                else => return null,
            }
        }
        if (!any_field_write) return null;
        return entries.toOwnedSlice(self.alloc) catch null;
    }

    fn emitSimdExpr(
        self: *Emitter,
        loop_id: usize,
        tw: usize,
        elem_param: []const u8,
        locals: []const SimdLocalVar,
        expr: *const ast.Expr,
        target_ty: *const sema.Ty,
    ) Io.Writer.Error!void {
        switch (expr.*) {
            .field => |fld| {
                if (fld.target.* == .ident and std.mem.eql(u8, self.sourceOf(fld.target.ident), elem_param)) {
                    try self.w.print("__vec_{d}_", .{loop_id});
                    try self.emitIdent(self.sourceOf(fld.name));
                    return;
                }
            },
            .ident => |sp| {
                const name = self.sourceOf(sp);
                for (locals) |lv| {
                    if (std.mem.eql(u8, lv.name, name)) {
                        try self.w.print("__vloc_{d}_", .{loop_id});
                        try self.emitIdent(name);
                        return;
                    }
                }
            },
            .unary => |u| {
                if (u.op == .neg) {
                    try self.w.writeAll("(-(");
                    try self.emitSimdExpr(loop_id, tw, elem_param, locals, u.operand, target_ty);
                    try self.w.writeAll("))");
                    return;
                }
            },
            .binary => |b| {
                if (b.op == .div and target_ty.isInteger() != null) {
                    try self.w.writeAll("@divTrunc(");
                    try self.emitSimdExpr(loop_id, tw, elem_param, locals, b.left, target_ty);
                    try self.w.writeAll(", ");
                    try self.emitSimdExpr(loop_id, tw, elem_param, locals, b.right, target_ty);
                    try self.w.writeByte(')');
                    return;
                }
                if (b.op == .add or b.op == .sub or b.op == .mul or b.op == .div) {
                    try self.w.writeByte('(');
                    try self.emitSimdExpr(loop_id, tw, elem_param, locals, b.left, target_ty);
                    try self.w.print(" {s} ", .{b.op.symbol()});
                    try self.emitSimdExpr(loop_id, tw, elem_param, locals, b.right, target_ty);
                    try self.w.writeByte(')');
                    return;
                }
            },
            else => {},
        }
        try self.w.print("@as(@Vector({d}, ", .{tw});
        try self.emitTy(target_ty);
        try self.w.writeAll("), @splat(");
        try self.emitCoercedExpr(expr, target_ty);
        try self.w.writeAll("))");
    }

    fn containsName(list: []const []const u8, name: []const u8) bool {
        for (list) |item| {
            if (std.mem.eql(u8, item, name)) return true;
        }
        return false;
    }

    fn collectPatternBinders(self: *const Emitter, pat: *const ast.Pattern, locals: *std.ArrayList([]const u8)) void {
        switch (pat.*) {
            .ident => |id| locals.append(self.alloc, self.sourceOf(id.name)) catch {},
            .tuple => |tp| for (tp.elems) |el| self.collectPatternBinders(el, locals),
            .constructor => |c| for (c.args) |a| self.collectPatternBinders(a.pattern, locals),
            .alias => |al| {
                self.collectPatternBinders(al.inner, locals);
                locals.append(self.alloc, self.sourceOf(al.name)) catch {};
            },
            .list => |lp| {
                for (lp.elems) |el| self.collectPatternBinders(el, locals);
                if (lp.rest) |rsp| locals.append(self.alloc, self.sourceOf(rsp)) catch {};
            },
            .or_pat => |op| if (op.alternatives.len > 0) self.collectPatternBinders(op.alternatives[0], locals),
            else => {},
        }
    }

    fn collectCapturesBlock(
        self: *const Emitter,
        root_blk: *const ast.Block,
        blk: *const ast.Block,
        locals: *std.ArrayList([]const u8),
        caps: *std.ArrayList(ForkCapture),
    ) void {
        const lmark = locals.items.len;
        defer locals.shrinkRetainingCapacity(lmark);
        for (blk.stmts) |*st| {
            self.collectCapturesStmt(root_blk, st, locals, caps);
        }
        if (blk.tail) |t| self.collectCapturesExpr(root_blk, t, locals, caps);
    }

    fn collectCapturesStmt(
        self: *const Emitter,
        root_blk: *const ast.Block,
        stmt: *const ast.Stmt,
        locals: *std.ArrayList([]const u8),
        caps: *std.ArrayList(ForkCapture),
    ) void {
        switch (stmt.*) {
            .let_stmt => |ls| {
                self.collectCapturesExpr(root_blk, ls.value, locals, caps);
                self.collectPatternBinders(ls.pattern, locals);
            },
            .use_stmt => |us| {
                self.collectCapturesExpr(root_blk, us.expr, locals, caps);
                for (us.patterns) |p| self.collectPatternBinders(p, locals);
            },
            .assign_stmt => |asg| {
                self.collectCapturesExpr(root_blk, asg.target, locals, caps);
                self.collectCapturesExpr(root_blk, asg.value, locals, caps);
            },
            .return_stmt => |rs| if (rs.value) |v| self.collectCapturesExpr(root_blk, v, locals, caps),
            .while_stmt => |ws| {
                self.collectCapturesExpr(root_blk, ws.cond, locals, caps);
                self.collectCapturesBlock(root_blk, &ws.body, locals, caps);
            },
            .for_stmt => |fs| {
                self.collectCapturesExpr(root_blk, fs.iter, locals, caps);
                const lmark = locals.items.len;
                defer locals.shrinkRetainingCapacity(lmark);
                self.collectPatternBinders(fs.pattern, locals);
                self.collectCapturesBlock(root_blk, &fs.body, locals, caps);
            },
            .expr_stmt => |es| self.collectCapturesExpr(root_blk, es.expr, locals, caps),
        }
    }

    fn collectCapturesExpr(
        self: *const Emitter,
        root_blk: *const ast.Block,
        expr: *const ast.Expr,
        locals: *std.ArrayList([]const u8),
        caps: *std.ArrayList(ForkCapture),
    ) void {
        switch (expr.*) {
            .ident => |sp| {
                const name = self.sourceOf(sp);
                if (containsName(locals.items, name)) return;
                const sv = self.lookupScopeVar(name) orelse return;
                for (caps.items) |c| {
                    if (std.mem.eql(u8, c.name, name)) return;
                }
                const ty = sv.ty orelse self.checked.exprType(expr) orelse return;
                const is_ptr_or_slice = isPointerType(ty) or ty.* == .slice or ty.* == .collection or
                    (ty.* == .view and (ty.view.target.* == .slice or ty.view.target.* == .collection)) or
                    (ty.* == .path_borrow and (ty.path_borrow.base.* == .slice or ty.path_borrow.base.* == .collection));
                const by_ptr = sv.is_mut and !is_ptr_or_slice and self.blockMutatesOrBorrowsIdent(root_blk, name);
                caps.append(self.alloc, .{ .name = name, .ty = ty, .by_ptr = by_ptr }) catch {};
            },
            .unary => |u| self.collectCapturesExpr(root_blk, u.operand, locals, caps),
            .binary => |b| {
                self.collectCapturesExpr(root_blk, b.left, locals, caps);
                self.collectCapturesExpr(root_blk, b.right, locals, caps);
            },
            .cast => |c| self.collectCapturesExpr(root_blk, c.expr, locals, caps),
            .call => |c| {
                self.collectCapturesExpr(root_blk, c.callee, locals, caps);
                for (c.args) |a| self.collectCapturesExpr(root_blk, a.value, locals, caps);
            },
            .field => |fld| self.collectCapturesExpr(root_blk, fld.target, locals, caps),
            .index => |ix| {
                self.collectCapturesExpr(root_blk, ix.target, locals, caps);
                self.collectCapturesExpr(root_blk, ix.idx, locals, caps);
            },
            .try_op => |t| self.collectCapturesExpr(root_blk, t.operand, locals, caps),
            .record_lit => |rl| {
                for (rl.fields) |rf| {
                    if (rf.value) |v| {
                        self.collectCapturesExpr(root_blk, v, locals, caps);
                    } else {
                        const name = self.sourceOf(rf.name);
                        if (!containsName(locals.items, name)) {
                            if (self.lookupScopeVar(name)) |sv| {
                                var already = false;
                                for (caps.items) |c| if (std.mem.eql(u8, c.name, name)) {
                                    already = true;
                                };
                                if (!already) {
                                    if (sv.ty) |ty| {
                                        const is_ptr_or_slice = isPointerType(ty) or ty.* == .slice or ty.* == .collection;
                                        const by_ptr = sv.is_mut and !is_ptr_or_slice and self.blockMutatesOrBorrowsIdent(root_blk, name);
                                        caps.append(self.alloc, .{ .name = name, .ty = ty, .by_ptr = by_ptr }) catch {};
                                    }
                                }
                            }
                        }
                    }
                }
            },
            .tuple => |tp| for (tp.elems) |el| self.collectCapturesExpr(root_blk, el, locals, caps),
            .list => |ls| for (ls.elems) |el| self.collectCapturesExpr(root_blk, el, locals, caps),
            .block => |*blk| self.collectCapturesBlock(root_blk, blk, locals, caps),
            .if_expr => |ie| {
                self.collectCapturesExpr(root_blk, ie.cond, locals, caps);
                self.collectCapturesBlock(root_blk, &ie.then_block, locals, caps);
                if (ie.else_branch) |eb| self.collectCapturesExpr(root_blk, eb, locals, caps);
            },
            .case_expr => |ce| {
                for (ce.subjects) |s| self.collectCapturesExpr(root_blk, s, locals, caps);
                for (ce.arms) |arm| {
                    const lmark = locals.items.len;
                    defer locals.shrinkRetainingCapacity(lmark);
                    if (arm.alternatives.len > 0) {
                        for (arm.alternatives[0]) |p| self.collectPatternBinders(p, locals);
                    }
                    if (arm.guard) |g| self.collectCapturesExpr(root_blk, g, locals, caps);
                    self.collectCapturesExpr(root_blk, arm.body, locals, caps);
                }
            },
            .lambda => |lam| {
                const lmark = locals.items.len;
                defer locals.shrinkRetainingCapacity(lmark);
                for (lam.params) |p| locals.append(self.alloc, self.sourceOf(p.name)) catch {};
                self.collectCapturesBlock(root_blk, &lam.body, locals, caps);
            },
            .view_expr => |vw| {
                self.collectCapturesExpr(root_blk, vw.target, locals, caps);
                const lmark = locals.items.len;
                defer locals.shrinkRetainingCapacity(lmark);
                if (vw.binding) |bspan| locals.append(self.alloc, self.sourceOf(bspan)) catch {};
                self.collectCapturesBlock(root_blk, &vw.body, locals, caps);
            },
            .fork_expr => |fk| for (fk.branches) |*br| self.collectCapturesBlock(root_blk, br, locals, caps),
            .todo_expr => |td| if (td.message) |m| self.collectCapturesExpr(root_blk, m, locals, caps),
            .panic_expr => |pn| if (pn.message) |m| self.collectCapturesExpr(root_blk, m, locals, caps),
            else => {},
        }
    }

    fn collectFreeCaptures(self: *const Emitter, br: *const ast.Block) ![]const ForkCapture {
        var locals: std.ArrayList([]const u8) = .empty;
        var caps: std.ArrayList(ForkCapture) = .empty;
        self.collectCapturesBlock(br, br, &locals, &caps);
        return try caps.toOwnedSlice(self.alloc);
    }

    fn collectFreeLambdaCaptures(self: *const Emitter, lam: anytype) ![]const ForkCapture {
        var locals: std.ArrayList([]const u8) = .empty;
        for (lam.params) |p| {
            locals.append(self.alloc, self.sourceOf(p.name)) catch {};
        }
        var caps: std.ArrayList(ForkCapture) = .empty;
        self.collectCapturesBlock(&lam.body, &lam.body, &locals, &caps);
        return try caps.toOwnedSlice(self.alloc);
    }

    fn emitLambdaExpr(self: *Emitter, full_expr: *const ast.Expr, lam: anytype) Io.Writer.Error!void {
        const fn_ty_opt = self.checked.exprType(full_expr);
        const fn_info = if (fn_ty_opt) |ft| if (ft.* == .fn_ty) ft.fn_ty else null else null;
        const ret_ty: ?*const sema.Ty = if (fn_info) |fi| fi.ret else null;
        const ret_is_void = if (ret_ty) |rt| isVoidTy(rt) else (lam.ret == null and lam.body.tail == null);
        const caps = self.collectFreeLambdaCaptures(lam) catch &.{};

        if (caps.len == 0) {
            try self.w.writeAll("(&((struct {\n");
            self.indent += 1;
            try self.writeIndent();
            try self.w.writeAll("pub fn call(");
        } else {
            try self.w.writeAll("(struct {\n");
            self.indent += 1;
            for (caps) |cap| {
                try self.writeIndent();
                try self.emitIdent(cap.name);
                try self.w.writeAll(": ");
                if (cap.by_ptr) try self.w.writeByte('*');
                try self.emitTy(cap.ty);
                try self.w.writeAll(",\n");
            }
            try self.writeIndent();
            try self.w.writeAll("pub fn call(__ctx: @This()");
        }

        for (lam.params, 0..) |p, pi| {
            if (caps.len > 0 or pi > 0) try self.w.writeAll(", ");
            try self.emitIdent(self.sourceOf(p.name));
            try self.w.writeAll(": ");
            if (fn_info != null and pi < fn_info.?.params.len and fn_info.?.params[pi].* != .err) {
                if (fn_info.?.params[pi].* == .fn_ty) {
                    try self.w.writeAll("anytype");
                } else {
                    try self.emitTy(fn_info.?.params[pi]);
                }
            } else if (p.ty) |pt| {
                try self.emitAstType(pt);
            } else {
                try self.w.writeAll("usize");
            }
        }
        try self.w.writeAll(") ");
        if (ret_ty != null and ret_ty.?.* != .err) {
            try self.emitTy(ret_ty.?);
        } else if (lam.ret) |rt| {
            try self.emitAstType(rt);
        } else {
            try self.w.writeAll("void");
        }
        try self.w.writeAll(" {\n");

        self.indent += 1;
        const prev_ret = self.current_fn_ret;
        const prev_deref = self.deref_idents;
        const prev_ctx_vals = self.ctx_value_idents;
        const prev_scopes = self.scope_vars;
        self.current_fn_ret = ret_ty;
        var w_deref: std.ArrayList([]const u8) = .empty;
        var w_ctx_vals: std.ArrayList([]const u8) = .empty;
        var w_scopes: std.ArrayList(ScopeVar) = .empty;
        for (caps) |cap| {
            if (cap.by_ptr) {
                w_deref.append(self.alloc, cap.name) catch {};
            } else {
                w_ctx_vals.append(self.alloc, cap.name) catch {};
            }
            w_scopes.append(self.alloc, .{ .name = cap.name, .ty = cap.ty, .is_mut = cap.by_ptr }) catch {};
        }
        for (lam.params, 0..) |p, pi| {
            const pty: ?*const sema.Ty = if (fn_info != null and pi < fn_info.?.params.len) fn_info.?.params[pi] else null;
            const pname = self.sourceOf(p.name);
            w_scopes.append(self.alloc, .{
                .name = pname,
                .ty = pty,
                .is_mut = p.mutable or (pty != null and isPointerType(pty.?)),
            }) catch {};
            if (!self.blockMentionsIdent(&lam.body, pname)) {
                try self.writeIndent();
                try self.w.writeAll("_ = ");
                try self.emitIdent(pname);
                try self.w.writeAll(";\n");
            }
        }
        self.deref_idents = w_deref;
        self.ctx_value_idents = w_ctx_vals;
        self.scope_vars = w_scopes;
        defer {
            self.current_fn_ret = prev_ret;
            self.deref_idents = prev_deref;
            self.ctx_value_idents = prev_ctx_vals;
            self.scope_vars = prev_scopes;
        }

        try self.emitStmtsWithRest(lam.body.stmts, lam.body.tail);
        if (lam.body.tail) |t| {
            if (ret_is_void) {
                try self.emitTailStmt(t);
            } else {
                try self.writeIndent();
                try self.w.writeAll("return ");
                if (ret_ty != null and ret_ty.?.* != .err) {
                    try self.emitCoercedExpr(t, ret_ty.?);
                } else {
                    try self.emitExpr(t);
                }
                try self.w.writeAll(";\n");
            }
        }

        self.indent -= 1;
        try self.writeIndent();
        try self.w.writeAll("}\n");
        self.indent -= 1;
        try self.writeIndent();
        if (caps.len == 0) {
            try self.w.writeAll("}).call))");
        } else {
            try self.w.writeAll("}){ ");
            for (caps, 0..) |cap, ci| {
                if (ci > 0) try self.w.writeAll(", ");
                try self.w.writeByte('.');
                try self.emitIdent(cap.name);
                try self.w.writeAll(" = ");
                if (cap.by_ptr) try self.w.writeByte('&');
                if (self.isDerefIdent_slice(prev_deref.items, cap.name)) {
                    try self.w.writeAll("(__ctx.");
                    try self.emitIdent(cap.name);
                    try self.w.writeAll(".*)");
                } else if (self.isDerefIdent_slice(prev_ctx_vals.items, cap.name)) {
                    try self.w.writeAll("__ctx.");
                    try self.emitIdent(cap.name);
                } else {
                    try self.emitIdent(cap.name);
                }
            }
            try self.w.writeAll(" }");
        }
    }

    fn isDerefIdent_slice(self: *const Emitter, list: []const []const u8, name: []const u8) bool {
        _ = self;
        for (list) |item| if (std.mem.eql(u8, item, name)) return true;
        return false;
    }

    const CollectionPipeline = struct {
        base: *const ast.Expr,
        map_stages: []const *const ast.Expr,
        fold_arg: ?*const ast.Expr,
        fold_init: ?*const ast.Expr,
    };

    fn flattenCollectionPipeline(self: *const Emitter, expr: *const ast.Expr) CollectionPipeline {
        var cur = expr;
        var fold_arg: ?*const ast.Expr = null;
        var fold_init: ?*const ast.Expr = null;
        var stages: std.ArrayList(*const ast.Expr) = .empty;

        if (cur.* == .binary and cur.binary.op == .pipe and cur.binary.right.* == .call) {
            const c = cur.binary.right.call;
            if (c.callee.* == .ident and std.mem.eql(u8, self.sourceOf(c.callee.ident), "fold") and c.args.len == 2) {
                const l_ty = self.checked.exprType(cur.binary.left);
                if (l_ty != null and (l_ty.?.* == .collection or l_ty.?.* == .vec or l_ty.?.* == .slice or l_ty.?.* == .view or l_ty.?.* == .path_borrow)) {
                    fold_init = c.args[0].value;
                    fold_arg = c.args[1].value;
                    cur = cur.binary.left;
                }
            }
        }

        while (cur.* == .binary and cur.binary.op == .pipe and cur.binary.right.* == .call) {
            const c = cur.binary.right.call;
            if (c.callee.* == .ident and std.mem.eql(u8, self.sourceOf(c.callee.ident), "map_in_place") and
                c.args.len == 1 and c.args[0].value.* == .lambda)
            {
                stages.append(self.alloc, c.args[0].value) catch break;
                cur = cur.binary.left;
            } else {
                break;
            }
        }

        std.mem.reverse(*const ast.Expr, stages.items);
        return .{
            .base = cur,
            .map_stages = stages.toOwnedSlice(self.alloc) catch &.{},
            .fold_arg = fold_arg,
            .fold_init = fold_init,
        };
    }

    const SimdFoldSpec = struct {
        elem_param: []const u8,
        expr: *const ast.Expr,
        acc_ty: *const sema.Ty,
        fields: []SimdFieldEntry,
    };

    fn isIdentNamed(self: *const Emitter, e: *const ast.Expr, name: []const u8) bool {
        return e.* == .ident and std.mem.eql(u8, self.sourceOf(e.ident), name);
    }

    fn detectSimdWrapAddFold(
        self: *Emitter,
        elem_ridx_opt: ?usize,
        pipe: CollectionPipeline,
        fold_res_ty: ?*const sema.Ty,
    ) ?SimdFoldSpec {
        const ri = elem_ridx_opt orelse return null;
        if (ri >= self.checked.records.len) return null;
        const rec = &self.checked.records[ri];
        if (recHasPackedBins(rec)) return null;
        const fty = fold_res_ty orelse return null;
        if (fty.isInteger() == null or isSimdPrimitiveTy(fty) == null) return null;
        const fa = pipe.fold_arg orelse return null;
        if (fa.* != .lambda) return null;
        const lam = fa.lambda;
        if (lam.params.len != 2 or lam.body.stmts.len != 0 or lam.body.tail == null) return null;
        const tail = lam.body.tail.?;
        if (tail.* != .binary or tail.binary.op != .add_wrap) return null;
        const acc_p = self.sourceOf(lam.params[0].name);
        const elem_p = self.sourceOf(lam.params[1].name);
        const rhs_expr: *const ast.Expr = if (self.isIdentNamed(tail.binary.left, acc_p))
            tail.binary.right
        else if (self.isIdentNamed(tail.binary.right, acc_p))
            tail.binary.left
        else
            return null;
        var entries: std.ArrayList(SimdFieldEntry) = .empty;
        if (!self.isValidSimdExprForTy(rec, elem_p, &.{}, &entries, rhs_expr, fty)) return null;
        return .{
            .elem_param = elem_p,
            .expr = rhs_expr,
            .acc_ty = fty,
            .fields = entries.toOwnedSlice(self.alloc) catch return null,
        };
    }

    fn mergeSimdFieldEntries(
        self: *Emitter,
        base_opt: ?[]SimdFieldEntry,
        extra: []const SimdFieldEntry,
    ) ?[]SimdFieldEntry {
        var list: std.ArrayList(SimdFieldEntry) = .empty;
        if (base_opt) |base| list.appendSlice(self.alloc, base) catch return null;
        for (extra) |ex| {
            var found = false;
            for (list.items) |*item| {
                if (item.fidx == ex.fidx) {
                    item.read = item.read or ex.read;
                    item.written = item.written or ex.written;
                    found = true;
                    break;
                }
            }
            if (!found) list.append(self.alloc, ex) catch return null;
        }
        return list.toOwnedSlice(self.alloc) catch null;
    }

    fn isValidSimdAssignStmt(
        self: *Emitter,
        rec: *const sema.CheckedRecord,
        elem_param: []const u8,
        locals: []const SimdLocalVar,
        entries: *std.ArrayList(SimdFieldEntry),
        st: ast.Stmt,
        allow_ident_target: bool,
        inside_branch: bool,
    ) ?bool {
        if (st != .assign_stmt) return null;
        const asg = st.assign_stmt;
        switch (asg.op) {
            .assign, .add_assign, .sub_assign, .mul_assign, .div_assign => {},
            else => return null,
        }
        if (asg.target.* == .field) {
            const fld = asg.target.field;
            if (fld.target.* != .ident) return null;
            if (!std.mem.eql(u8, self.sourceOf(fld.target.ident), elem_param)) return null;
            const fname = self.sourceOf(fld.name);
            const idx = self.findOrAddSimdField(entries, rec, fname) orelse return null;
            const lhs_ty = entries.items[idx].ty;
            if (asg.op != .assign or inside_branch) entries.items[idx].read = true;
            entries.items[idx].written = true;
            if (!self.isValidSimdExprForTy(rec, elem_param, locals, entries, asg.value, lhs_ty)) return null;
            return true;
        } else if (allow_ident_target and asg.target.* == .ident) {
            const tname = self.sourceOf(asg.target.ident);
            var l_ty: ?*const sema.Ty = null;
            for (locals) |lv| {
                if (std.mem.eql(u8, lv.name, tname)) {
                    l_ty = lv.ty;
                    break;
                }
            }
            const lhs_ty = l_ty orelse return null;
            if (!self.isValidSimdExprForTy(rec, elem_param, locals, entries, asg.value, lhs_ty)) return null;
            return false;
        }
        return null;
    }

    fn isValidSimdIfExpr(
        self: *Emitter,
        rec: *const sema.CheckedRecord,
        elem_param: []const u8,
        locals: []const SimdLocalVar,
        entries: *std.ArrayList(SimdFieldEntry),
        ie: anytype,
    ) ?bool {
        if (self.isValidSimdCmpExpr(rec, elem_param, locals, entries, ie.cond) == null) return null;
        if (ie.then_block.tail != null or ie.then_block.stmts.len == 0) return null;
        var any_write = false;
        for (ie.then_block.stmts) |tst| {
            const wf = self.isValidSimdAssignStmt(rec, elem_param, locals, entries, tst, false, true) orelse return null;
            if (wf) any_write = true;
        }
        if (ie.else_branch) |eb| {
            if (eb.* != .block or eb.block.tail != null or eb.block.stmts.len == 0) return null;
            for (eb.block.stmts) |est| {
                const wf = self.isValidSimdAssignStmt(rec, elem_param, locals, entries, est, false, true) orelse return null;
                if (wf) any_write = true;
            }
        }
        return any_write;
    }

    fn emitSimdSelectAssign(
        self: *Emitter,
        id: usize,
        stage_idx: usize,
        tw: usize,
        elem_param: []const u8,
        simd_locals: []const SimdLocalVar,
        rec_p: *const sema.CheckedRecord,
        asg: anytype,
        mlbl: usize,
        select_on_true: bool,
    ) Io.Writer.Error!void {
        const fname = self.sourceOf(asg.target.field.name);
        const fi = findRecordFieldIdx(rec_p, fname).?;
        const fty = rec_p.fields[fi].ty;
        try self.writeIndent();
        try self.w.print("__vec_{d}_", .{id});
        try self.emitIdent(fname);
        try self.w.writeAll(" = @select(");
        try self.emitTy(fty);
        try self.w.print(", __vmask_{d}, ", .{mlbl});
        if (!select_on_true) {
            try self.w.print("__vec_{d}_", .{id});
            try self.emitIdent(fname);
            try self.w.writeAll(", ");
        }
        if (asg.op == .div_assign and fty.isInteger() != null) {
            try self.w.print("@divTrunc(__vec_{d}_", .{id});
            try self.emitIdent(fname);
            try self.w.writeAll(", ");
            try self.emitSimdStageExpr(id, stage_idx, tw, elem_param, simd_locals, asg.value, fty);
            try self.w.writeByte(')');
        } else if (asg.op != .assign) {
            const bin_op: []const u8 = switch (asg.op) {
                .add_assign => "+",
                .sub_assign => "-",
                .mul_assign => "*",
                .div_assign => "/",
                else => "+",
            };
            try self.w.print("(__vec_{d}_", .{id});
            try self.emitIdent(fname);
            try self.w.print(" {s} ", .{bin_op});
            try self.emitSimdStageExpr(id, stage_idx, tw, elem_param, simd_locals, asg.value, fty);
            try self.w.writeByte(')');
        } else {
            try self.emitSimdStageExpr(id, stage_idx, tw, elem_param, simd_locals, asg.value, fty);
        }
        if (select_on_true) {
            try self.w.print(", __vec_{d}_", .{id});
            try self.emitIdent(fname);
        }
        try self.w.writeAll(");\n");
    }

    fn emitSimdIfPredication(
        self: *Emitter,
        id: usize,
        stage_idx: usize,
        tw: usize,
        elem_param: []const u8,
        simd_locals: []const SimdLocalVar,
        rec_p: *const sema.CheckedRecord,
        ie: anytype,
    ) Io.Writer.Error!void {
        const cmp_ty = self.inferSimdExprScalarTy(rec_p, simd_locals, ie.cond.binary.left) orelse
            self.inferSimdExprScalarTy(rec_p, simd_locals, ie.cond.binary.right).?;
        const mlbl = self.nextLabel();
        try self.writeIndent();
        try self.w.print("const __vmask_{d}: @Vector({d}, bool) = (", .{ mlbl, tw });
        try self.emitSimdStageExpr(id, stage_idx, tw, elem_param, simd_locals, ie.cond.binary.left, cmp_ty);
        try self.w.print(" {s} ", .{ie.cond.binary.op.symbol()});
        try self.emitSimdStageExpr(id, stage_idx, tw, elem_param, simd_locals, ie.cond.binary.right, cmp_ty);
        try self.w.writeAll(");\n");
        for (ie.then_block.stmts) |tst| {
            if (tst != .assign_stmt or tst.assign_stmt.target.* != .field) continue;
            try self.emitSimdSelectAssign(id, stage_idx, tw, elem_param, simd_locals, rec_p, tst.assign_stmt, mlbl, true);
        }
        if (ie.else_branch) |eb| {
            if (eb.* == .block) {
                for (eb.block.stmts) |est| {
                    if (est != .assign_stmt or est.assign_stmt.target.* != .field) continue;
                    try self.emitSimdSelectAssign(id, stage_idx, tw, elem_param, simd_locals, rec_p, est.assign_stmt, mlbl, false);
                }
            }
        }
    }

    fn collectSimdMultiLambda(
        self: *Emitter,
        rec: *const sema.CheckedRecord,
        stage_lambdas: []const *const ast.Expr,
    ) ?[]SimdFieldEntry {
        if (stage_lambdas.len == 0) return null;
        var entries: std.ArrayList(SimdFieldEntry) = .empty;
        for (stage_lambdas) |lam_expr| {
            const lam = lam_expr.lambda;
            const elem_param = if (lam.params.len > 0) self.sourceOf(lam.params[0].name) else "__elem";
            if (lam.body.stmts.len == 0 and lam.body.tail == null) return null;
            var locals: std.ArrayList(SimdLocalVar) = .empty;
            var any_write = false;
            for (lam.body.stmts) |st| {
                switch (st) {
                    .let_stmt => |ls| {
                        if (ls.pattern.* != .ident) return null;
                        const lname = self.sourceOf(ls.pattern.ident.name);
                        const lty = self.checked.letType(ls.span.start) orelse self.checked.exprType(ls.value) orelse return null;
                        if (isSimdPrimitiveTy(lty) == null) return null;
                        if (!self.isValidSimdExprForTy(rec, elem_param, locals.items, &entries, ls.value, lty)) return null;
                        locals.append(self.alloc, .{ .name = lname, .ty = lty }) catch return null;
                    },
                    .assign_stmt => {
                        const wf = self.isValidSimdAssignStmt(rec, elem_param, locals.items, &entries, st, true, false) orelse return null;
                        if (wf) any_write = true;
                    },
                    .expr_stmt => |es| {
                        if (es.expr.* != .if_expr) return null;
                        const wf = self.isValidSimdIfExpr(rec, elem_param, locals.items, &entries, es.expr.if_expr) orelse return null;
                        if (wf) any_write = true;
                    },
                    else => return null,
                }
            }
            if (lam.body.tail) |tail| {
                if (tail.* != .if_expr) return null;
                const wf = self.isValidSimdIfExpr(rec, elem_param, locals.items, &entries, tail.if_expr) orelse return null;
                if (wf) any_write = true;
            }
            if (!any_write) return null;
        }
        return entries.toOwnedSlice(self.alloc) catch null;
    }

    const RecordFieldUsage = struct {
        reads: []bool,
        writes: []bool,
        whole_escaped: bool = false,
    };

    fn recHasPackedBins(rec: *const sema.CheckedRecord) bool {
        if (rec.is_flat_c) return false;
        for (0..rec.fields.len) |fi| {
            if (fieldBinByte(rec, fi) != null) return true;
        }
        return false;
    }

    fn collectBlockFieldUsage(
        self: *const Emitter,
        rec: *const sema.CheckedRecord,
        elem_param: []const u8,
        blk: *const ast.Block,
    ) RecordFieldUsage {
        const reads = self.alloc.alloc(bool, rec.fields.len) catch return .{ .reads = &.{}, .writes = &.{}, .whole_escaped = true };
        const writes = self.alloc.alloc(bool, rec.fields.len) catch return .{ .reads = &.{}, .writes = &.{}, .whole_escaped = true };
        @memset(reads, false);
        @memset(writes, false);
        var usage = RecordFieldUsage{ .reads = reads, .writes = writes, .whole_escaped = false };
        for (blk.stmts) |*st| {
            self.collectStmtFieldUsage(rec, elem_param, st, &usage);
        }
        if (blk.tail) |t| {
            self.collectExprFieldUsage(rec, elem_param, t, &usage);
        }
        return usage;
    }

    fn collectStmtFieldUsage(
        self: *const Emitter,
        rec: *const sema.CheckedRecord,
        elem_param: []const u8,
        stmt: *const ast.Stmt,
        usage: *RecordFieldUsage,
    ) void {
        switch (stmt.*) {
            .let_stmt => |ls| self.collectExprFieldUsage(rec, elem_param, ls.value, usage),
            .use_stmt => |us| self.collectExprFieldUsage(rec, elem_param, us.expr, usage),
            .assign_stmt => |asg| {
                if (asg.target.* == .field) {
                    const fld = asg.target.field;
                    if (fld.target.* == .ident and std.mem.eql(u8, self.sourceOf(fld.target.ident), elem_param)) {
                        if (findRecordFieldIdx(rec, self.sourceOf(fld.name))) |fi| {
                            usage.writes[fi] = true;
                            if (asg.op != .assign) usage.reads[fi] = true;
                        } else {
                            usage.whole_escaped = true;
                        }
                        self.collectExprFieldUsage(rec, elem_param, asg.value, usage);
                        return;
                    }
                }
                self.collectExprFieldUsage(rec, elem_param, asg.target, usage);
                self.collectExprFieldUsage(rec, elem_param, asg.value, usage);
            },
            .return_stmt => |rs| if (rs.value) |v| self.collectExprFieldUsage(rec, elem_param, v, usage),
            .while_stmt => |ws| {
                self.collectExprFieldUsage(rec, elem_param, ws.cond, usage);
                for (ws.body.stmts) |*st| self.collectStmtFieldUsage(rec, elem_param, st, usage);
                if (ws.body.tail) |t| self.collectExprFieldUsage(rec, elem_param, t, usage);
            },
            .for_stmt => |fs| {
                self.collectExprFieldUsage(rec, elem_param, fs.iter, usage);
                for (fs.body.stmts) |*st| self.collectStmtFieldUsage(rec, elem_param, st, usage);
                if (fs.body.tail) |t| self.collectExprFieldUsage(rec, elem_param, t, usage);
            },
            .expr_stmt => |es| self.collectExprFieldUsage(rec, elem_param, es.expr, usage),
        }
    }

    fn collectExprFieldUsage(
        self: *const Emitter,
        rec: *const sema.CheckedRecord,
        elem_param: []const u8,
        expr: *const ast.Expr,
        usage: *RecordFieldUsage,
    ) void {
        switch (expr.*) {
            .ident => |sp| {
                if (std.mem.eql(u8, self.sourceOf(sp), elem_param)) {
                    usage.whole_escaped = true;
                }
            },
            .field => |fld| {
                if (fld.target.* == .ident and std.mem.eql(u8, self.sourceOf(fld.target.ident), elem_param)) {
                    if (findRecordFieldIdx(rec, self.sourceOf(fld.name))) |fi| {
                        usage.reads[fi] = true;
                    } else {
                        usage.whole_escaped = true;
                    }
                    return;
                }
                self.collectExprFieldUsage(rec, elem_param, fld.target, usage);
            },
            .unary => |u| self.collectExprFieldUsage(rec, elem_param, u.operand, usage),
            .binary => |b| {
                self.collectExprFieldUsage(rec, elem_param, b.left, usage);
                self.collectExprFieldUsage(rec, elem_param, b.right, usage);
            },
            .cast => |c| self.collectExprFieldUsage(rec, elem_param, c.expr, usage),
            .call => |c| {
                self.collectExprFieldUsage(rec, elem_param, c.callee, usage);
                for (c.args) |a| self.collectExprFieldUsage(rec, elem_param, a.value, usage);
            },
            .index => |ix| {
                self.collectExprFieldUsage(rec, elem_param, ix.target, usage);
                self.collectExprFieldUsage(rec, elem_param, ix.idx, usage);
            },
            .try_op => |t| self.collectExprFieldUsage(rec, elem_param, t.operand, usage),
            .record_lit => |rl| {
                for (rl.fields) |rf| {
                    if (rf.value) |v| {
                        self.collectExprFieldUsage(rec, elem_param, v, usage);
                    } else if (std.mem.eql(u8, self.sourceOf(rf.name), elem_param)) {
                        usage.whole_escaped = true;
                    }
                }
            },
            .tuple => |tp| for (tp.elems) |el| self.collectExprFieldUsage(rec, elem_param, el, usage),
            .list => |ls| for (ls.elems) |el| self.collectExprFieldUsage(rec, elem_param, el, usage),
            .block => |*blk| {
                for (blk.stmts) |*st| self.collectStmtFieldUsage(rec, elem_param, st, usage);
                if (blk.tail) |t| self.collectExprFieldUsage(rec, elem_param, t, usage);
            },
            .if_expr => |ie| {
                self.collectExprFieldUsage(rec, elem_param, ie.cond, usage);
                for (ie.then_block.stmts) |*st| self.collectStmtFieldUsage(rec, elem_param, st, usage);
                if (ie.then_block.tail) |t| self.collectExprFieldUsage(rec, elem_param, t, usage);
                if (ie.else_branch) |eb| self.collectExprFieldUsage(rec, elem_param, eb, usage);
            },
            .case_expr => |ce| {
                for (ce.subjects) |s| self.collectExprFieldUsage(rec, elem_param, s, usage);
                for (ce.arms) |arm| {
                    if (arm.guard) |g| self.collectExprFieldUsage(rec, elem_param, g, usage);
                    self.collectExprFieldUsage(rec, elem_param, arm.body, usage);
                }
            },
            .lambda => |lam| {
                for (lam.params) |p| {
                    if (std.mem.eql(u8, self.sourceOf(p.name), elem_param)) return;
                }
                for (lam.body.stmts) |*st| self.collectStmtFieldUsage(rec, elem_param, st, usage);
                if (lam.body.tail) |t| self.collectExprFieldUsage(rec, elem_param, t, usage);
            },
            .view_expr => |vw| {
                self.collectExprFieldUsage(rec, elem_param, vw.target, usage);
                for (vw.body.stmts) |*st| self.collectStmtFieldUsage(rec, elem_param, st, usage);
                if (vw.body.tail) |t| self.collectExprFieldUsage(rec, elem_param, t, usage);
            },
            .fork_expr => |fk| for (fk.branches) |*br| {
                for (br.stmts) |*st| self.collectStmtFieldUsage(rec, elem_param, st, usage);
                if (br.tail) |t| self.collectExprFieldUsage(rec, elem_param, t, usage);
            },
            .using_expr => |ue| self.collectExprFieldUsage(rec, elem_param, ue.target, usage),
            .todo_expr => |td| if (td.message) |m| self.collectExprFieldUsage(rec, elem_param, m, usage),
            .panic_expr => |pn| if (pn.message) |m| self.collectExprFieldUsage(rec, elem_param, m, usage),
            else => {},
        }
    }

    fn emitSelectiveCollectionStage(
        self: *Emitter,
        id: usize,
        elem_ridx_opt: ?usize,
        elem_ptr_ty: ?*const sema.Ty,
        is_phys_soa: bool,
        is_phys_aosoa: bool,
        aosoa_tw: usize,
        lam_expr: *const ast.Expr,
        idx_expr: []const u8,
    ) Io.Writer.Error!void {
        const lam = lam_expr.lambda;
        const elem_param = if (lam.params.len > 0) self.sourceOf(lam.params[0].name) else "__elem";
        try self.writeIndent();
        try self.w.writeAll("{\n");
        self.indent += 1;
        const sv = self.pushScopeVars();
        defer self.popScopeVars(sv);
        self.bindScopeVar(elem_param, elem_ptr_ty, true);

        const rec_opt: ?*const sema.CheckedRecord = if (elem_ridx_opt) |ri|
            (if (ri < self.checked.records.len) &self.checked.records[ri] else null)
        else
            null;
        var use_selective = false;
        var usage: RecordFieldUsage = .{ .reads = &.{}, .writes = &.{}, .whole_escaped = true };
        if ((is_phys_soa or is_phys_aosoa) and rec_opt != null and !recHasPackedBins(rec_opt.?)) {
            usage = self.collectBlockFieldUsage(rec_opt.?, elem_param, &lam.body);
            if (!usage.whole_escaped) {
                use_selective = true;
            }
        }

        if (use_selective) {
            const rec = rec_opt.?;
            const slbl = self.nextLabel();
            if (is_phys_aosoa) {
                try self.writeIndent();
                try self.w.print("const __si_{d}: usize = __col_{d}.base_elem + ({s});\n", .{ slbl, id, idx_expr });
                try self.writeIndent();
                try self.w.print("const __st_{d} = &__col_{d}.tiles[__si_{d} / {d}];\n", .{ slbl, id, slbl, aosoa_tw });
                try self.writeIndent();
                try self.w.print("const __sl_{d}: usize = __si_{d} % {d};\n", .{ slbl, slbl, aosoa_tw });
            }
            try self.writeIndent();
            try self.w.print("var __el_{d}: ", .{id});
            try self.emitIdent(rec.name);
            try self.w.writeAll(" = undefined;\n");
            for (rec.fields, 0..) |f, fi| {
                if (!usage.reads[fi]) continue;
                try self.writeIndent();
                try self.w.print("__el_{d}.", .{id});
                try self.emitIdent(f.name);
                if (is_phys_aosoa) {
                    try self.w.print(" = __st_{d}.", .{slbl});
                    try self.emitIdent(f.name);
                    try self.w.print("[__sl_{d}];\n", .{slbl});
                } else {
                    try self.w.print(" = __col_{d}.", .{id});
                    try self.emitIdent(f.name);
                    try self.w.print("[{s}];\n", .{idx_expr});
                }
            }
            try self.writeIndent();
            try self.w.writeAll("const ");
            try self.emitIdent(elem_param);
            try self.w.print(" = &__el_{d};\n", .{id});
            if (!self.blockMentionsIdent(&lam.body, elem_param)) {
                try self.writeIndent();
                try self.w.writeAll("_ = ");
                try self.emitIdent(elem_param);
                try self.w.writeAll(";\n");
            }
            try self.emitStmtsWithRest(lam.body.stmts, lam.body.tail);
            if (lam.body.tail) |t| try self.emitTailStmt(t);
            for (rec.fields, 0..) |f, fi| {
                if (!usage.writes[fi]) continue;
                try self.writeIndent();
                if (is_phys_aosoa) {
                    try self.w.print("__st_{d}.", .{slbl});
                    try self.emitIdent(f.name);
                    try self.w.print("[__sl_{d}] = __el_{d}.", .{ slbl, id });
                } else {
                    try self.w.print("__col_{d}.", .{id});
                    try self.emitIdent(f.name);
                    try self.w.print("[{s}] = __el_{d}.", .{ idx_expr, id });
                }
                try self.emitIdent(f.name);
                try self.w.writeAll(";\n");
            }
        } else {
            if (is_phys_soa or is_phys_aosoa) {
                try self.writeIndent();
                try self.w.print("var __el_{d} = __col_{d}.get({s});\n", .{ id, id, idx_expr });
                try self.writeIndent();
                try self.w.writeAll("const ");
                try self.emitIdent(elem_param);
                try self.w.print(" = &__el_{d};\n", .{id});
            } else {
                try self.writeIndent();
                try self.w.writeAll("const ");
                try self.emitIdent(elem_param);
                try self.w.print(" = &__col_{d}[{s}];\n", .{ id, idx_expr });
            }
            if (!self.blockMentionsIdent(&lam.body, elem_param)) {
                try self.writeIndent();
                try self.w.writeAll("_ = ");
                try self.emitIdent(elem_param);
                try self.w.writeAll(";\n");
            }
            try self.emitStmtsWithRest(lam.body.stmts, lam.body.tail);
            if (lam.body.tail) |t| try self.emitTailStmt(t);
            if (is_phys_soa or is_phys_aosoa) {
                try self.writeIndent();
                try self.w.print("__col_{d}.set({s}, __el_{d});\n", .{ id, idx_expr, id });
            }
        }
        self.indent -= 1;
        try self.writeIndent();
        try self.w.writeAll("}\n");
    }

    fn emitCollectionFoldStep(
        self: *Emitter,
        id: usize,
        pipe: CollectionPipeline,
        elem_ridx_opt: ?usize,
        is_phys_soa: bool,
        is_phys_aosoa: bool,
        aosoa_tw: usize,
        idx_expr: []const u8,
    ) Io.Writer.Error!void {
        const rec_opt: ?*const sema.CheckedRecord = if (elem_ridx_opt) |ri|
            (if (ri < self.checked.records.len) &self.checked.records[ri] else null)
        else
            null;
        if ((is_phys_soa or is_phys_aosoa) and rec_opt != null and !recHasPackedBins(rec_opt.?) and
            pipe.fold_arg.?.* == .lambda and pipe.fold_arg.?.lambda.params.len == 2)
        {
            const rec = rec_opt.?;
            const lam = pipe.fold_arg.?.lambda;
            const elem_param = self.sourceOf(lam.params[1].name);
            const usage = self.collectBlockFieldUsage(rec, elem_param, &lam.body);
            if (!usage.whole_escaped) {
                const flbl = self.nextLabel();
                try self.writeIndent();
                try self.w.writeAll("{\n");
                self.indent += 1;
                if (is_phys_aosoa) {
                    try self.writeIndent();
                    try self.w.print("const __fi_{d}: usize = __col_{d}.base_elem + ({s});\n", .{ flbl, id, idx_expr });
                    try self.writeIndent();
                    try self.w.print("const __ft_{d} = &__col_{d}.tiles[__fi_{d} / {d}];\n", .{ flbl, id, flbl, aosoa_tw });
                    try self.writeIndent();
                    try self.w.print("const __fl_{d}: usize = __fi_{d} % {d};\n", .{ flbl, flbl, aosoa_tw });
                }
                try self.writeIndent();
                try self.w.print("var __fel_{d}: ", .{flbl});
                try self.emitIdent(rec.name);
                try self.w.writeAll(" = undefined;\n");
                for (rec.fields, 0..) |f, fi| {
                    if (!usage.reads[fi]) continue;
                    try self.writeIndent();
                    try self.w.print("__fel_{d}.", .{flbl});
                    try self.emitIdent(f.name);
                    if (is_phys_aosoa) {
                        try self.w.print(" = __ft_{d}.", .{flbl});
                        try self.emitIdent(f.name);
                        try self.w.print("[__fl_{d}];\n", .{flbl});
                    } else {
                        try self.w.print(" = __col_{d}.", .{id});
                        try self.emitIdent(f.name);
                        try self.w.print("[{s}];\n", .{idx_expr});
                    }
                }
                try self.writeIndent();
                try self.w.print("__acc_{d} = aethelCall(", .{id});
                try self.emitExpr(pipe.fold_arg.?);
                try self.w.print(", .{{ __acc_{d}, __fel_{d} }});\n", .{ id, flbl });
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("}\n");
                return;
            }
        }
        try self.writeIndent();
        try self.w.print("__acc_{d} = aethelCall(", .{id});
        try self.emitExpr(pipe.fold_arg.?);
        if (is_phys_soa or is_phys_aosoa) {
            try self.w.print(", .{{ __acc_{d}, __col_{d}.get({s}) }});\n", .{ id, id, idx_expr });
        } else {
            try self.w.print(", .{{ __acc_{d}, __col_{d}[{s}] }});\n", .{ id, id, idx_expr });
        }
    }

    fn emitCollectionPipeline(
        self: *Emitter,
        full_expr: ?*const ast.Expr,
        pipe: CollectionPipeline,
        need_value: bool,
    ) Io.Writer.Error!void {
        const recv_ty = self.checked.exprType(pipe.base);
        var tile_width: ?usize = null;
        var elem_ridx_opt: ?usize = null;
        if (recv_ty) |rt| {
            const ridx_opt: ?usize = switch (rt.*) {
                .collection => |c| c.elem_record,
                .vec => |v| v.elem_record,
                .slice => |s| if (s.elem.* == .record) s.elem.record else null,
                .view => |v| switch (v.target.*) {
                    .collection => |c| c.elem_record,
                    .vec => |vc| vc.elem_record,
                    .slice => |s| if (s.elem.* == .record) s.elem.record else null,
                    .record => |ri| ri,
                    else => null,
                },
                .path_borrow => |pb| switch (pb.base.*) {
                    .collection => |c| c.elem_record,
                    .vec => |vc| vc.elem_record,
                    .slice => |s| if (s.elem.* == .record) s.elem.record else null,
                    .record => |ri| ri,
                    else => null,
                },
                else => null,
            };
            elem_ridx_opt = ridx_opt;
            if (ridx_opt) |ridx| {
                if (ridx < self.checked.records.len) {
                    if (self.checked.records[ridx].collection_layout) |cl| {
                        switch (cl) {
                            .aosoa => |w| tile_width = w,
                            .soa => {
                                if (pipe.map_stages.len > 0 and
                                    self.collectSimdMultiLambda(&self.checked.records[ridx], pipe.map_stages) != null)
                                {
                                    tile_width = 8;
                                }
                            },
                            else => {},
                        }
                    }
                }
            }
        }
        const elem_ptr_ty: ?*const sema.Ty = if (elem_ridx_opt) |ri| blk: {
            const rec_ty = self.alloc.create(sema.Ty) catch break :blk null;
            rec_ty.* = .{ .record = ri };
            const ptr_ty = self.alloc.create(sema.Ty) catch break :blk null;
            ptr_ty.* = .{ .view = .{ .mode = .exclusive, .target = rec_ty, .target_record = ri } };
            break :blk ptr_ty;
        } else null;

        const id = self.nextLabel();
        const is_fold = pipe.fold_arg != null;
        const returns_val = is_fold or need_value;
        const fold_res_ty: ?*const sema.Ty = if (is_fold and full_expr != null) self.checked.exprType(full_expr.?) else null;
        const simd_fold_opt: ?SimdFoldSpec = if (is_fold and elem_ridx_opt != null)
            self.detectSimdWrapAddFold(elem_ridx_opt, pipe, fold_res_ty)
        else
            null;
        if (tile_width == null and simd_fold_opt != null and elem_ridx_opt != null) {
            if (self.checked.records[elem_ridx_opt.?].collection_layout) |cl| {
                if (cl == .soa) tile_width = 8;
            }
        }

        if (returns_val) {
            try self.w.print("blk_{d}: {{\n", .{id});
        } else {
            try self.w.writeAll("{\n");
        }
        self.indent += 1;

        if (pipe.map_stages.len >= 2 or is_fold) {
            try self.writeIndent();
            try self.w.print("// Categorical fusion: {d} map_in_place stage(s){s} fused into 1 pass\n", .{
                pipe.map_stages.len,
                if (is_fold) " + fold deforestation" else "",
            });
        }

        const elem_bk: ?BackingKind = if (elem_ridx_opt) |ri|
            (if (ri < self.checked.records.len) recordBackingKind(&self.checked.records[ri]) else null)
        else
            null;
        const is_phys_soa = elem_bk != null and elem_bk.? == .soa;
        const is_phys_aosoa = elem_bk != null and elem_bk.? == .aosoa;
        const is_vec_base = self.isVecTyOrViewToVec(recv_ty);
        const returns_vec_raw = is_vec_base and !is_fold and need_value;

        try self.writeIndent();
        if (returns_vec_raw) {
            try self.w.print("var __raw_{d} = ", .{id});
            try self.emitCoercedExpr(pipe.base, recv_ty.?);
            try self.w.writeAll(";\n");
            try self.writeIndent();
            try self.w.print("const __col_{d} = __raw_{d}.", .{ id, id });
            if (is_phys_soa or is_phys_aosoa) {
                try self.w.writeAll(if (pipe.map_stages.len > 0) "mutView()" else "asView()");
            } else {
                try self.w.writeAll(if (pipe.map_stages.len > 0) "mutSlice()" else "asSlice()");
            }
            try self.w.writeAll(";\n");
        } else if (is_vec_base) {
            try self.w.print("const __col_{d} = (", .{id});
            try self.emitExpr(pipe.base);
            try self.w.writeAll(").");
            if (is_phys_soa or is_phys_aosoa) {
                try self.w.writeAll(if (pipe.map_stages.len > 0) "mutView()" else "asView()");
            } else {
                try self.w.writeAll(if (pipe.map_stages.len > 0) "mutSlice()" else "asSlice()");
            }
            try self.w.writeAll(";\n");
        } else {
            try self.w.print("const __col_{d} = ", .{id});
            try self.emitExpr(pipe.base);
            try self.w.writeAll(";\n");
        }

        if (is_fold) {
            try self.writeIndent();
            try self.w.print("var __acc_{d}", .{id});
            if (fold_res_ty != null and fold_res_ty.?.* != .err) {
                try self.w.writeAll(": ");
                try self.emitTy(fold_res_ty.?);
            }
            try self.w.writeAll(" = ");
            if (fold_res_ty != null and fold_res_ty.?.* != .err) {
                try self.emitCoercedExpr(pipe.fold_init.?, fold_res_ty.?);
            } else {
                try self.emitExpr(pipe.fold_init.?);
            }
            try self.w.writeAll(";\n");
        }

        if (tile_width) |tw| {
            const raw_simd_fields: ?[]SimdFieldEntry = if (tw >= 2 and elem_ridx_opt != null and pipe.map_stages.len > 0)
                self.collectSimdMultiLambda(&self.checked.records[elem_ridx_opt.?], pipe.map_stages)
            else
                null;
            const active_fold_simd: ?SimdFoldSpec = if (tw >= 2 and simd_fold_opt != null and (pipe.map_stages.len == 0 or raw_simd_fields != null))
                simd_fold_opt
            else
                null;
            const simd_fields_opt: ?[]SimdFieldEntry = if (pipe.map_stages.len == 0)
                (if (active_fold_simd) |sf| self.mergeSimdFieldEntries(null, sf.fields) else null)
            else if (raw_simd_fields != null and active_fold_simd != null)
                self.mergeSimdFieldEntries(raw_simd_fields, active_fold_simd.?.fields)
            else
                raw_simd_fields;

            if (active_fold_simd) |af| {
                try self.writeIndent();
                try self.w.print("var __vacc_{d}: @Vector({d}, ", .{ id, tw });
                try self.emitTy(af.acc_ty);
                try self.w.writeAll(") = @splat(0);\n");
            }

            if (pipe.map_stages.len <= 1 and simd_fields_opt != null) {
                try self.writeIndent();
                if (is_phys_aosoa) {
                    try self.w.print("// @layout(aosoa({d})): L1-cache tiled 64B-aligned @Vector({d}, T) SIMD pass\n", .{ tw, tw });
                } else {
                    try self.w.print("// @layout(soa): @Vector({d}, T) SIMD pass over contiguous columns\n", .{tw});
                }
            } else if (pipe.map_stages.len >= 1) {
                try self.writeIndent();
                if (is_phys_aosoa) {
                    try self.w.print("// @layout(aosoa({d})): L1-cache tiled loop (tile_width = {d})\n", .{ tw, tw });
                } else {
                    try self.w.print("// @layout(soa): @Vector({d}, T) fused SIMD loop\n", .{tw});
                }
            }

            try self.writeIndent();
            try self.w.print("var __tile_{d}: usize = 0;\n", .{id});
            if (is_phys_aosoa) {
                try self.writeIndent();
                try self.w.print("if (__col_{d}.base_elem % {d} == 0) {{\n", .{ id, tw });
                self.indent += 1;
            }
            try self.writeIndent();
            try self.w.print("while (__tile_{d} + {d} <= __col_{d}.len) : (__tile_{d} += {d}) {{\n", .{ id, tw, id, id, tw });
            self.indent += 1;

            if (simd_fields_opt) |simd_fields| {
                for (simd_fields) |sf| {
                    try self.writeIndent();
                    try self.w.writeAll(if (sf.written) "var " else "const ");
                    try self.w.print("__vec_{d}_", .{id});
                    try self.emitIdent(sf.name);
                    try self.w.print(": @Vector({d}, ", .{tw});
                    try self.emitTy(sf.ty);
                    if (sf.read) {
                        if (is_phys_aosoa) {
                            try self.w.print(") = __col_{d}.tiles[(__col_{d}.base_elem + __tile_{d}) / {d}].", .{ id, id, id, tw });
                            try self.emitIdent(sf.name);
                            try self.w.writeAll(";\n");
                        } else if (is_phys_soa) {
                            try self.w.print(") = __col_{d}.", .{id});
                            try self.emitIdent(sf.name);
                            try self.w.print("[__tile_{d}..][0..{d}].*;\n", .{ id, tw });
                        } else {
                            const ld_lbl = self.nextLabel();
                            try self.w.print(") = blk_{d}: {{\n", .{ld_lbl});
                            self.indent += 1;
                            try self.writeIndent();
                            try self.w.print("var __buf_{d}: [{d}]", .{ ld_lbl, tw });
                            try self.emitTy(sf.ty);
                            try self.w.writeAll(" align(64) = undefined;\n");
                            try self.writeIndent();
                            try self.w.print("inline for (0..{d}) |__li| __buf_{d}[__li] = __col_{d}[__tile_{d} + __li].", .{ tw, ld_lbl, id, id });
                            try self.emitIdent(sf.name);
                            try self.w.writeAll(";\n");
                            try self.writeIndent();
                            try self.w.print("break :blk_{d} __buf_{d};\n", .{ ld_lbl, ld_lbl });
                            self.indent -= 1;
                            try self.writeIndent();
                            try self.w.writeAll("};\n");
                        }
                    } else {
                        try self.w.writeAll(") = undefined;\n");
                    }
                }

                for (pipe.map_stages, 0..) |lam_expr, stage_idx| {
                    const lam = lam_expr.lambda;
                    const elem_param = if (lam.params.len > 0) self.sourceOf(lam.params[0].name) else "__elem";
                    var simd_locals: std.ArrayList(SimdLocalVar) = .empty;
                    for (lam.body.stmts, 0..) |st, si| {
                        switch (st) {
                            .let_stmt => |ls| {
                                const lname = self.sourceOf(ls.pattern.ident.name);
                                const lty = self.checked.letType(ls.span.start) orelse self.checked.exprType(ls.value).?;
                                const is_mut_loc = ls.mutable or ls.pattern.ident.mutable;
                                try self.writeIndent();
                                try self.w.writeAll(if (is_mut_loc) "var " else "const ");
                                try self.w.print("__vloc_{d}_{d}_", .{ id, stage_idx });
                                try self.emitIdent(lname);
                                try self.w.print(": @Vector({d}, ", .{tw});
                                try self.emitTy(lty);
                                try self.w.writeAll(") = ");
                                try self.emitSimdStageExpr(id, stage_idx, tw, elem_param, simd_locals.items, ls.value, lty);
                                try self.w.writeAll(";\n");
                                if (is_mut_loc and !self.stmtsMutateOrBorrowIdent(lam.body.stmts[si + 1 ..], null, lname)) {
                                    try self.writeIndent();
                                    try self.w.print("_ = &__vloc_{d}_{d}_", .{ id, stage_idx });
                                    try self.emitIdent(lname);
                                    try self.w.writeAll(";\n");
                                } else if (!is_mut_loc and !self.stmtsMentionIdent(lam.body.stmts[si + 1 ..], null, lname)) {
                                    try self.writeIndent();
                                    try self.w.print("_ = __vloc_{d}_{d}_", .{ id, stage_idx });
                                    try self.emitIdent(lname);
                                    try self.w.writeAll(";\n");
                                }
                                simd_locals.append(self.alloc, .{ .name = lname, .ty = lty }) catch {};
                            },
                            .assign_stmt => |asg| {
                                var lhs_ty: *const sema.Ty = undefined;
                                try self.writeIndent();
                                if (asg.target.* == .field) {
                                    const fname = self.sourceOf(asg.target.field.name);
                                    const fi = findRecordFieldIdx(&self.checked.records[elem_ridx_opt.?], fname).?;
                                    lhs_ty = self.checked.records[elem_ridx_opt.?].fields[fi].ty;
                                    if (asg.op == .div_assign and lhs_ty.isInteger() != null) {
                                        try self.w.print("__vec_{d}_", .{id});
                                        try self.emitIdent(fname);
                                        try self.w.print(" = @divTrunc(__vec_{d}_", .{id});
                                        try self.emitIdent(fname);
                                        try self.w.writeAll(", ");
                                        try self.emitSimdStageExpr(id, stage_idx, tw, elem_param, simd_locals.items, asg.value, lhs_ty);
                                        try self.w.writeAll(");\n");
                                        continue;
                                    }
                                    try self.w.print("__vec_{d}_", .{id});
                                    try self.emitIdent(fname);
                                } else {
                                    const lname = self.sourceOf(asg.target.ident);
                                    for (simd_locals.items) |lv| {
                                        if (std.mem.eql(u8, lv.name, lname)) {
                                            lhs_ty = lv.ty;
                                            break;
                                        }
                                    }
                                    if (asg.op == .div_assign and lhs_ty.isInteger() != null) {
                                        try self.w.print("__vloc_{d}_{d}_", .{ id, stage_idx });
                                        try self.emitIdent(lname);
                                        try self.w.print(" = @divTrunc(__vloc_{d}_{d}_", .{ id, stage_idx });
                                        try self.emitIdent(lname);
                                        try self.w.writeAll(", ");
                                        try self.emitSimdStageExpr(id, stage_idx, tw, elem_param, simd_locals.items, asg.value, lhs_ty);
                                        try self.w.writeAll(");\n");
                                        continue;
                                    }
                                    try self.w.print("__vloc_{d}_{d}_", .{ id, stage_idx });
                                    try self.emitIdent(lname);
                                }
                                try self.w.print(" {s} ", .{asg.op.symbol()});
                                try self.emitSimdStageExpr(id, stage_idx, tw, elem_param, simd_locals.items, asg.value, lhs_ty);
                                try self.w.writeAll(";\n");
                            },
                            .expr_stmt => |es| {
                                if (es.expr.* == .if_expr) {
                                    try self.emitSimdIfPredication(id, stage_idx, tw, elem_param, simd_locals.items, &self.checked.records[elem_ridx_opt.?], es.expr.if_expr);
                                }
                            },
                            else => {},
                        }
                    }
                    if (lam.body.tail) |tail| {
                        if (tail.* == .if_expr) {
                            try self.emitSimdIfPredication(id, stage_idx, tw, elem_param, simd_locals.items, &self.checked.records[elem_ridx_opt.?], tail.if_expr);
                        }
                    }
                }

                if (is_phys_aosoa) {
                    for (simd_fields) |sf| {
                        if (!sf.written) continue;
                        try self.writeIndent();
                        try self.w.print("__col_{d}.tiles[(__col_{d}.base_elem + __tile_{d}) / {d}].", .{ id, id, id, tw });
                        try self.emitIdent(sf.name);
                        try self.w.print(" = @as([{d}]", .{tw});
                        try self.emitTy(sf.ty);
                        try self.w.print(", __vec_{d}_", .{id});
                        try self.emitIdent(sf.name);
                        try self.w.writeAll(");\n");
                    }
                    if (active_fold_simd) |af| {
                        try self.writeIndent();
                        try self.w.print("__vacc_{d} +%= ", .{id});
                        try self.emitSimdStageExpr(id, 0, tw, af.elem_param, &.{}, af.expr, af.acc_ty);
                        try self.w.writeAll(";\n");
                    } else if (is_fold) {
                        try self.writeIndent();
                        try self.w.print("inline for (0..{d}) |__li| {{\n", .{tw});
                        self.indent += 1;
                        const fold_idx_s = std.fmt.allocPrint(self.alloc, "__tile_{d} + __li", .{id}) catch unreachable;
                        try self.emitCollectionFoldStep(id, pipe, elem_ridx_opt, is_phys_soa, is_phys_aosoa, tw, fold_idx_s);
                        self.indent -= 1;
                        try self.writeIndent();
                        try self.w.writeAll("}\n");
                    }
                } else if (is_phys_soa) {
                    for (simd_fields) |sf| {
                        if (!sf.written) continue;
                        try self.writeIndent();
                        try self.w.print("__col_{d}.", .{id});
                        try self.emitIdent(sf.name);
                        try self.w.print("[__tile_{d}..][0..{d}].* = @as([{d}]", .{ id, tw, tw });
                        try self.emitTy(sf.ty);
                        try self.w.print(", __vec_{d}_", .{id});
                        try self.emitIdent(sf.name);
                        try self.w.writeAll(");\n");
                    }
                    if (active_fold_simd) |af| {
                        try self.writeIndent();
                        try self.w.print("__vacc_{d} +%= ", .{id});
                        try self.emitSimdStageExpr(id, 0, tw, af.elem_param, &.{}, af.expr, af.acc_ty);
                        try self.w.writeAll(";\n");
                    } else if (is_fold) {
                        try self.writeIndent();
                        try self.w.print("inline for (0..{d}) |__li| {{\n", .{tw});
                        self.indent += 1;
                        const fold_idx_s = std.fmt.allocPrint(self.alloc, "__tile_{d} + __li", .{id}) catch unreachable;
                        try self.emitCollectionFoldStep(id, pipe, elem_ridx_opt, is_phys_soa, is_phys_aosoa, tw, fold_idx_s);
                        self.indent -= 1;
                        try self.writeIndent();
                        try self.w.writeAll("}\n");
                    }
                } else {
                    if (pipe.map_stages.len > 0) {
                        try self.writeIndent();
                        try self.w.print("inline for (0..{d}) |__li| {{\n", .{tw});
                        self.indent += 1;
                        for (simd_fields) |sf| {
                            if (!sf.written) continue;
                            try self.writeIndent();
                            try self.w.print("__col_{d}[__tile_{d} + __li].", .{ id, id });
                            try self.emitIdent(sf.name);
                            try self.w.print(" = __vec_{d}_", .{id});
                            try self.emitIdent(sf.name);
                            try self.w.writeAll("[__li];\n");
                        }
                        if (is_fold and active_fold_simd == null) {
                            const fold_idx_s = std.fmt.allocPrint(self.alloc, "__tile_{d} + __li", .{id}) catch unreachable;
                            try self.emitCollectionFoldStep(id, pipe, elem_ridx_opt, is_phys_soa, is_phys_aosoa, tw, fold_idx_s);
                        }
                        self.indent -= 1;
                        try self.writeIndent();
                        try self.w.writeAll("}\n");
                    }
                    if (active_fold_simd) |af| {
                        try self.writeIndent();
                        try self.w.print("__vacc_{d} +%= ", .{id});
                        try self.emitSimdStageExpr(id, 0, tw, af.elem_param, &.{}, af.expr, af.acc_ty);
                        try self.w.writeAll(";\n");
                    }
                }
            } else {
                try self.writeIndent();
                try self.w.print("var __lane_{d}: usize = 0;\n", .{id});
                try self.writeIndent();
                try self.w.print("while (__lane_{d} < {d}) : (__lane_{d} += 1) {{\n", .{ id, tw, id });
                self.indent += 1;
                const lane_idx_s = std.fmt.allocPrint(self.alloc, "__tile_{d} + __lane_{d}", .{ id, id }) catch unreachable;
                for (pipe.map_stages) |lam_expr| {
                    try self.emitSelectiveCollectionStage(id, elem_ridx_opt, elem_ptr_ty, is_phys_soa, is_phys_aosoa, tw, lam_expr, lane_idx_s);
                }
                if (is_fold) {
                    try self.emitCollectionFoldStep(id, pipe, elem_ridx_opt, is_phys_soa, is_phys_aosoa, tw, lane_idx_s);
                }
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("}\n");
            }

            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeAll("}\n");
            if (is_phys_aosoa) {
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("}\n");
            }
            if (active_fold_simd != null) {
                try self.writeIndent();
                try self.w.print("__acc_{d} +%= @reduce(.Add, __vacc_{d});\n", .{ id, id });
            }
            try self.writeIndent();
            try self.w.print("while (__tile_{d} < __col_{d}.len) : (__tile_{d} += 1) {{\n", .{ id, id, id });
            self.indent += 1;
            const tail_idx_s = std.fmt.allocPrint(self.alloc, "__tile_{d}", .{id}) catch unreachable;
            for (pipe.map_stages) |lam_expr| {
                try self.emitSelectiveCollectionStage(id, elem_ridx_opt, elem_ptr_ty, is_phys_soa, is_phys_aosoa, tw, lam_expr, tail_idx_s);
            }
            if (is_fold) {
                try self.emitCollectionFoldStep(id, pipe, elem_ridx_opt, is_phys_soa, is_phys_aosoa, tw, tail_idx_s);
            }
            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeAll("}\n");
        } else {
            try self.writeIndent();
            try self.w.print("var __idx_{d}: usize = 0;\n", .{id});
            try self.writeIndent();
            try self.w.print("while (__idx_{d} < __col_{d}.len) : (__idx_{d} += 1) {{\n", .{ id, id, id });
            self.indent += 1;
            const scalar_idx_s = std.fmt.allocPrint(self.alloc, "__idx_{d}", .{id}) catch unreachable;
            for (pipe.map_stages) |lam_expr| {
                try self.emitSelectiveCollectionStage(id, elem_ridx_opt, elem_ptr_ty, is_phys_soa, is_phys_aosoa, 0, lam_expr, scalar_idx_s);
            }
            if (is_fold) {
                try self.emitCollectionFoldStep(id, pipe, elem_ridx_opt, is_phys_soa, is_phys_aosoa, 0, scalar_idx_s);
            }
            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeAll("}\n");
        }

        if (is_fold) {
            try self.writeIndent();
            try self.w.print("break :blk_{d} __acc_{d};\n", .{ id, id });
        } else if (returns_vec_raw) {
            try self.writeIndent();
            try self.w.print("break :blk_{d} __raw_{d};\n", .{ id, id });
        } else if (returns_val) {
            try self.writeIndent();
            try self.w.print("break :blk_{d} __col_{d};\n", .{ id, id });
        }
        self.indent -= 1;
        try self.writeIndent();
        try self.w.writeByte('}');
    }

    fn emitSimdStageExpr(
        self: *Emitter,
        loop_id: usize,
        stage_idx: usize,
        tw: usize,
        elem_param: []const u8,
        locals: []const SimdLocalVar,
        expr: *const ast.Expr,
        target_ty: *const sema.Ty,
    ) Io.Writer.Error!void {
        switch (expr.*) {
            .field => |fld| {
                if (fld.target.* == .ident and std.mem.eql(u8, self.sourceOf(fld.target.ident), elem_param)) {
                    try self.w.print("__vec_{d}_", .{loop_id});
                    try self.emitIdent(self.sourceOf(fld.name));
                    return;
                }
            },
            .ident => |sp| {
                const name = self.sourceOf(sp);
                for (locals) |lv| {
                    if (std.mem.eql(u8, lv.name, name)) {
                        try self.w.print("__vloc_{d}_{d}_", .{ loop_id, stage_idx });
                        try self.emitIdent(name);
                        return;
                    }
                }
            },
            .unary => |u| {
                if (u.op == .neg) {
                    try self.w.writeAll("(-(");
                    try self.emitSimdStageExpr(loop_id, stage_idx, tw, elem_param, locals, u.operand, target_ty);
                    try self.w.writeAll("))");
                    return;
                }
            },
            .binary => |b| {
                if (b.op == .div and target_ty.isInteger() != null) {
                    try self.w.writeAll("@divTrunc(");
                    try self.emitSimdStageExpr(loop_id, stage_idx, tw, elem_param, locals, b.left, target_ty);
                    try self.w.writeAll(", ");
                    try self.emitSimdStageExpr(loop_id, stage_idx, tw, elem_param, locals, b.right, target_ty);
                    try self.w.writeByte(')');
                    return;
                }
                if (b.op == .add or b.op == .sub or b.op == .mul or b.op == .div or
                    b.op == .add_wrap or b.op == .sub_wrap or b.op == .mul_wrap)
                {
                    try self.w.writeByte('(');
                    try self.emitSimdStageExpr(loop_id, stage_idx, tw, elem_param, locals, b.left, target_ty);
                    try self.w.print(" {s} ", .{b.op.symbol()});
                    try self.emitSimdStageExpr(loop_id, stage_idx, tw, elem_param, locals, b.right, target_ty);
                    try self.w.writeByte(')');
                    return;
                }
            },
            .cast => |c| {
                const src_ty = self.checked.exprType(c.expr) orelse blk: {
                    if (c.expr.* == .field and c.expr.field.target.* == .ident) {
                        const ridx_c = self.findCheckedRecordIndex(self.sourceOf(c.expr.field.target.ident));
                        _ = ridx_c;
                    }
                    break :blk target_ty;
                };
                try self.w.print("@as(@Vector({d}, ", .{tw});
                try self.emitTy(target_ty);
                try self.w.writeAll("), @intCast(");
                try self.emitSimdStageExpr(loop_id, stage_idx, tw, elem_param, locals, c.expr, src_ty);
                try self.w.writeAll("))");
                return;
            },
            .if_expr => |ie| {
                const cmp_ty = self.checked.exprType(ie.cond.binary.left) orelse
                    self.checked.exprType(ie.cond.binary.right) orelse target_ty;
                try self.w.writeAll("@select(");
                try self.emitTy(target_ty);
                try self.w.writeAll(", (");
                try self.emitSimdStageExpr(loop_id, stage_idx, tw, elem_param, locals, ie.cond.binary.left, cmp_ty);
                try self.w.print(" {s} ", .{ie.cond.binary.op.symbol()});
                try self.emitSimdStageExpr(loop_id, stage_idx, tw, elem_param, locals, ie.cond.binary.right, cmp_ty);
                try self.w.writeAll("), ");
                try self.emitSimdStageExpr(loop_id, stage_idx, tw, elem_param, locals, ie.then_block.tail.?, target_ty);
                try self.w.writeAll(", ");
                try self.emitSimdStageExpr(loop_id, stage_idx, tw, elem_param, locals, ie.else_branch.?.block.tail.?, target_ty);
                try self.w.writeByte(')');
                return;
            },
            else => {},
        }
        try self.w.print("@as(@Vector({d}, ", .{tw});
        try self.emitTy(target_ty);
        try self.w.writeAll("), @splat(");
        try self.emitCoercedExpr(expr, target_ty);
        try self.w.writeAll("))");
    }

    fn emitOptionResultCombinator(
        self: *Emitter,
        call_expr: ?*const ast.Expr,
        cname: []const u8,
        recv_expr: *const ast.Expr,
        recv_ty: *const sema.Ty,
        arg_val: *const ast.Expr,
    ) Io.Writer.Error!void {
        const res_ty: ?*const sema.Ty = if (call_expr) |ce| self.checked.exprType(ce) else null;
        const lbl = self.nextLabel();
        if (recv_ty.* == .option) {
            const inner_ty = recv_ty.option;
            if (std.mem.eql(u8, cname, "unwrap_or")) {
                try self.w.writeByte('(');
                try self.emitExpr(recv_expr);
                try self.w.writeAll(" orelse ");
                try self.emitCoercedExpr(arg_val, inner_ty);
                try self.w.writeByte(')');
                return;
            }
            if (std.mem.eql(u8, cname, "map")) {
                const out_inner: ?*const sema.Ty = if (res_ty != null and res_ty.?.* == .option) res_ty.?.option else null;
                try self.w.print("blk_{d}: {{\n", .{lbl});
                self.indent += 1;
                try self.writeIndent();
                try self.w.writeAll("if (");
                try self.emitExpr(recv_expr);
                try self.w.print(") |__val_{d}| {{\n", .{lbl});
                self.indent += 1;
                try self.writeIndent();
                try self.w.print("break :blk_{d} @as(?", .{lbl});
                if (out_inner != null and out_inner.?.* != .err) {
                    try self.emitTy(out_inner.?);
                } else {
                    try self.w.print("@TypeOf(aethelCall(", .{});
                    try self.emitExpr(arg_val);
                    try self.w.print(", .{{ __val_{d} }}))", .{lbl});
                }
                try self.w.writeAll(", aethelCall(");
                try self.emitExpr(arg_val);
                try self.w.print(", .{{ __val_{d} }}));\n", .{lbl});
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("} else {\n");
                self.indent += 1;
                try self.writeIndent();
                try self.w.print("break :blk_{d} null;\n", .{lbl});
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("}\n");
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeByte('}');
                return;
            }
            if (std.mem.eql(u8, cname, "and_then")) {
                try self.w.print("blk_{d}: {{\n", .{lbl});
                self.indent += 1;
                try self.writeIndent();
                try self.w.writeAll("if (");
                try self.emitExpr(recv_expr);
                try self.w.print(") |__val_{d}| {{\n", .{lbl});
                self.indent += 1;
                try self.writeIndent();
                try self.w.print("break :blk_{d} aethelCall(", .{lbl});
                try self.emitExpr(arg_val);
                try self.w.print(", .{{ __val_{d} }});\n", .{lbl});
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("} else {\n");
                self.indent += 1;
                try self.writeIndent();
                try self.w.print("break :blk_{d} null;\n", .{lbl});
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("}\n");
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeByte('}');
                return;
            }
            if (std.mem.eql(u8, cname, "ok_or")) {
                const err_ty: ?*const sema.Ty = if (res_ty != null and res_ty.?.* == .result) res_ty.?.result.err else self.checked.exprType(arg_val);
                try self.w.print("blk_{d}: {{\n", .{lbl});
                self.indent += 1;
                try self.writeIndent();
                try self.w.writeAll("if (");
                try self.emitExpr(recv_expr);
                try self.w.print(") |__val_{d}| {{\n", .{lbl});
                self.indent += 1;
                try self.writeIndent();
                try self.w.print("break :blk_{d} ", .{lbl});
                if (res_ty != null and res_ty.?.* == .result) try self.emitTy(res_ty.?);
                try self.w.print("{{ .Ok = __val_{d} }};\n", .{lbl});
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("} else {\n");
                self.indent += 1;
                try self.writeIndent();
                try self.w.print("break :blk_{d} ", .{lbl});
                if (res_ty != null and res_ty.?.* == .result) try self.emitTy(res_ty.?);
                try self.w.writeAll("{ .Err = ");
                if (err_ty != null and err_ty.?.* != .err) {
                    try self.emitCoercedExpr(arg_val, err_ty.?);
                } else {
                    try self.emitExpr(arg_val);
                }
                try self.w.writeAll(" };\n");
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("}\n");
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeByte('}');
                return;
            }
        }
        if (recv_ty.* == .result) {
            const ok_ty = recv_ty.result.ok;
            if (std.mem.eql(u8, cname, "unwrap_or")) {
                try self.w.print("blk_{d}: {{\n", .{lbl});
                self.indent += 1;
                try self.writeIndent();
                try self.w.writeAll("switch (");
                try self.emitExpr(recv_expr);
                try self.w.writeAll(") {\n");
                self.indent += 1;
                try self.writeIndent();
                try self.w.print(".Ok => |__val_{d}| break :blk_{d} __val_{d},\n", .{ lbl, lbl, lbl });
                try self.writeIndent();
                try self.w.print(".Err => break :blk_{d} ", .{lbl});
                try self.emitCoercedExpr(arg_val, ok_ty);
                try self.w.writeAll(",\n");
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("}\n");
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeByte('}');
                return;
            }
            if (std.mem.eql(u8, cname, "map")) {
                try self.w.print("blk_{d}: {{\n", .{lbl});
                self.indent += 1;
                try self.writeIndent();
                try self.w.writeAll("switch (");
                try self.emitExpr(recv_expr);
                try self.w.writeAll(") {\n");
                self.indent += 1;
                try self.writeIndent();
                try self.w.print(".Ok => |__val_{d}| break :blk_{d} ", .{ lbl, lbl });
                if (res_ty != null and res_ty.?.* == .result) try self.emitTy(res_ty.?);
                try self.w.writeAll("{ .Ok = aethelCall(");
                try self.emitExpr(arg_val);
                try self.w.print(", .{{ __val_{d} }}) }},\n", .{lbl});
                try self.writeIndent();
                try self.w.print(".Err => |__err_{d}| break :blk_{d} ", .{ lbl, lbl });
                if (res_ty != null and res_ty.?.* == .result) try self.emitTy(res_ty.?);
                try self.w.print("{{ .Err = __err_{d} }},\n", .{lbl});
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("}\n");
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeByte('}');
                return;
            }
            if (std.mem.eql(u8, cname, "and_then")) {
                try self.w.print("blk_{d}: {{\n", .{lbl});
                self.indent += 1;
                try self.writeIndent();
                try self.w.writeAll("switch (");
                try self.emitExpr(recv_expr);
                try self.w.writeAll(") {\n");
                self.indent += 1;
                try self.writeIndent();
                try self.w.print(".Ok => |__val_{d}| break :blk_{d} aethelCall(", .{ lbl, lbl });
                try self.emitExpr(arg_val);
                try self.w.print(", .{{ __val_{d} }}),\n", .{lbl});
                try self.writeIndent();
                try self.w.print(".Err => |__err_{d}| break :blk_{d} ", .{ lbl, lbl });
                if (res_ty != null and res_ty.?.* == .result) try self.emitTy(res_ty.?);
                try self.w.print("{{ .Err = __err_{d} }},\n", .{lbl});
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeAll("}\n");
                self.indent -= 1;
                try self.writeIndent();
                try self.w.writeByte('}');
                return;
            }
        }
    }

    fn emitFusedMapUnwrapOr(
        self: *Emitter,
        full_expr: *const ast.Expr,
        base_expr: *const ast.Expr,
        base_ty: *const sema.Ty,
        map_fn: *const ast.Expr,
        default_expr: *const ast.Expr,
    ) Io.Writer.Error!void {
        const lbl = self.nextLabel();
        const out_ty = self.checked.exprType(full_expr);
        try self.w.print("blk_{d}: {{\n", .{lbl});
        self.indent += 1;
        try self.writeIndent();
        if (base_ty.* == .option) {
            try self.w.writeAll("// Categorical fusion: Option.map |> unwrap_or\n");
            try self.writeIndent();
            try self.w.writeAll("if (");
            try self.emitExpr(base_expr);
            try self.w.print(") |__val_{d}| {{\n", .{lbl});
            self.indent += 1;
            try self.writeIndent();
            try self.w.print("break :blk_{d} aethelCall(", .{lbl});
            try self.emitExpr(map_fn);
            try self.w.print(", .{{ __val_{d} }});\n", .{lbl});
            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeAll("} else {\n");
            self.indent += 1;
            try self.writeIndent();
            try self.w.print("break :blk_{d} ", .{lbl});
            if (out_ty != null and out_ty.?.* != .err) {
                try self.emitCoercedExpr(default_expr, out_ty.?);
            } else {
                try self.emitExpr(default_expr);
            }
            try self.w.writeAll(";\n");
            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeAll("}\n");
        } else {
            try self.w.writeAll("// Categorical fusion: Result.map |> unwrap_or\n");
            try self.writeIndent();
            try self.w.writeAll("switch (");
            try self.emitExpr(base_expr);
            try self.w.writeAll(") {\n");
            self.indent += 1;
            try self.writeIndent();
            try self.w.print(".Ok => |__val_{d}| break :blk_{d} aethelCall(", .{ lbl, lbl });
            try self.emitExpr(map_fn);
            try self.w.print(", .{{ __val_{d} }}),\n", .{lbl});
            try self.writeIndent();
            try self.w.print(".Err => break :blk_{d} ", .{lbl});
            if (out_ty != null and out_ty.?.* != .err) {
                try self.emitCoercedExpr(default_expr, out_ty.?);
            } else {
                try self.emitExpr(default_expr);
            }
            try self.w.writeAll(",\n");
            self.indent -= 1;
            try self.writeIndent();
            try self.w.writeAll("}\n");
        }
        self.indent -= 1;
        try self.writeIndent();
        try self.w.writeByte('}');
    }
};

fn isZigKeyword(name: []const u8) bool {
    const kws = std.StaticStringMap(void).initComptime(.{
        .{ "addrspace", {} },  .{ "align", {} },       .{ "allowzero", {} },
        .{ "and", {} },        .{ "anyframe", {} },    .{ "anytype", {} },
        .{ "asm", {} },        .{ "async", {} },       .{ "await", {} },
        .{ "break", {} },      .{ "callconv", {} },    .{ "catch", {} },
        .{ "comptime", {} },   .{ "const", {} },       .{ "continue", {} },
        .{ "defer", {} },      .{ "else", {} },        .{ "enum", {} },
        .{ "errdefer", {} },   .{ "error", {} },       .{ "export", {} },
        .{ "extern", {} },     .{ "fn", {} },          .{ "for", {} },
        .{ "if", {} },         .{ "inline", {} },      .{ "linksection", {} },
        .{ "noalias", {} },    .{ "nosuspend", {} },   .{ "null", {} },
        .{ "opaque", {} },     .{ "or", {} },          .{ "orelse", {} },
        .{ "packed", {} },     .{ "pub", {} },         .{ "resume", {} },
        .{ "return", {} },     .{ "struct", {} },      .{ "suspend", {} },
        .{ "switch", {} },     .{ "test", {} },        .{ "threadlocal", {} },
        .{ "try", {} },        .{ "type", {} },        .{ "undefined", {} },
        .{ "union", {} },      .{ "unreachable", {} }, .{ "var", {} },
        .{ "volatile", {} },   .{ "while", {} },
    });
    return kws.has(name);
}
