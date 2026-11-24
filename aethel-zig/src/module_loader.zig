const std = @import("std");
const Io = std.Io;
const ast = @import("ast.zig");
const parser = @import("parser.zig");
const stdlib = @import("stdlib.zig");

pub const SourceSlice = struct {
    module_id: usize,
    path: []const u8,
    module_key: []const u8,
    start: usize,
    end: usize,
    source: [:0]const u8,
};

pub const LoadError = struct {
    path: []const u8,
    source: [:0]const u8,
    span: ast.Span,
    message: []const u8,
};

pub const MemoryFile = struct {
    module_key: []const u8,
    path: []const u8,
    source: [:0]const u8,
};

pub const LoadedProgram = struct {
    arena: std.heap.ArenaAllocator,
    combined_source: [:0]const u8,
    slices: []const SourceSlice,
    entry_module_id: usize,
    errors: []const LoadError,

    pub fn deinit(self: *LoadedProgram) void {
        self.arena.deinit();
    }

    pub fn hasErrors(self: *const LoadedProgram) bool {
        return self.errors.len > 0;
    }
};

pub const LocatedSpan = struct {
    slice: *const SourceSlice,
    local_span: ast.Span,
};

/// Map a byte span inside `combined_source` back to its originating file and local offsets.
pub fn locateSpan(slices: []const SourceSlice, span: ast.Span) ?LocatedSpan {
    if (slices.len == 0) return null;
    for (slices) |*sl| {
        if (span.start >= sl.start and span.start < sl.end) {
            const local_start = span.start - sl.start;
            const capped_end = @min(span.end, sl.end);
            const local_end = if (capped_end > sl.start) capped_end - sl.start else local_start;
            return .{
                .slice = sl,
                .local_span = .{ .start = local_start, .end = local_end },
            };
        }
    }
    // EOF / trailing position maps to the last non-empty slice (or last slice).
    var idx = slices.len;
    while (idx > 0) {
        idx -= 1;
        const sl = &slices[idx];
        if (span.start >= sl.start) {
            const clamped_start = @min(span.start - sl.start, sl.source.len);
            return .{
                .slice = sl,
                .local_span = .{ .start = clamped_start, .end = clamped_start },
            };
        }
    }
    return .{
        .slice = &slices[0],
        .local_span = .{ .start = 0, .end = 0 },
    };
}

const LoadedFile = struct {
    path: []const u8,
    module_key: []const u8,
    source: [:0]const u8,
    module_id: usize,
};

const Loader = struct {
    alloc: std.mem.Allocator,
    io: ?Io,
    memory_files: ?[]const MemoryFile,
    entry_dir: []const u8,
    visiting: std.ArrayList([]const u8) = .empty,
    loaded: std.ArrayList(LoadedFile) = .empty,
    errors: std.ArrayList(LoadError) = .empty,

    fn findLoadedByKey(self: *const Loader, norm_key: []const u8) ?usize {
        for (self.loaded.items, 0..) |item, i| {
            if (std.mem.eql(u8, item.path, norm_key) or std.mem.eql(u8, item.module_key, norm_key)) {
                return i;
            }
        }
        return null;
    }

    fn findLoadedByPath(self: *const Loader, norm_path: []const u8) ?usize {
        for (self.loaded.items, 0..) |item, i| {
            if (std.mem.eql(u8, item.path, norm_path)) return i;
        }
        return null;
    }

    fn isVisiting(self: *const Loader, norm_path: []const u8) bool {
        for (self.visiting.items) |p| {
            if (std.mem.eql(u8, p, norm_path)) return true;
        }
        return false;
    }

    fn dupeSentinelZ(alloc: std.mem.Allocator, s: []const u8) ![:0]const u8 {
        const buf = try alloc.allocSentinel(u8, s.len, 0);
        @memcpy(buf, s);
        return buf;
    }

    fn readSource(self: *Loader, path: []const u8) ?[:0]const u8 {
        if (self.memory_files) |mfs| {
            for (mfs) |mf| {
                if (std.mem.eql(u8, mf.path, path) or std.mem.eql(u8, mf.module_key, path)) {
                    return dupeSentinelZ(self.alloc, mf.source) catch null;
                }
            }
            return null;
        }
        const io = self.io orelse return null;
        return Io.Dir.cwd().readFileAllocOptions(
            io,
            path,
            self.alloc,
            .limited(16 * 1024 * 1024),
            .of(u8),
            0,
        ) catch null;
    }

    fn findMemoryFile(self: *const Loader, key_or_path: []const u8) ?MemoryFile {
        const mfs = self.memory_files orelse return null;
        for (mfs) |mf| {
            if (std.mem.eql(u8, mf.path, key_or_path) or std.mem.eql(u8, mf.module_key, key_or_path)) {
                return mf;
            }
        }
        return null;
    }

    fn normalizePath(alloc: std.mem.Allocator, raw: []const u8) ![]const u8 {
        var is_abs = raw.len > 0 and raw[0] == '/';
        var parts: std.ArrayList([]const u8) = .empty;
        var it = std.mem.tokenizeScalar(u8, raw, '/');
        while (it.next()) |seg| {
            if (std.mem.eql(u8, seg, ".")) continue;
            if (std.mem.eql(u8, seg, "..")) {
                if (parts.items.len > 0 and !std.mem.eql(u8, parts.items[parts.items.len - 1], "..")) {
                    _ = parts.pop();
                } else if (!is_abs) {
                    try parts.append(alloc, "..");
                }
                continue;
            }
            try parts.append(alloc, seg);
        }
        if (parts.items.len == 0) return if (is_abs) "/" else ".";
        var out: std.ArrayList(u8) = .empty;
        if (is_abs) try out.append(alloc, '/');
        for (parts.items, 0..) |p, idx| {
            if (idx > 0) try out.append(alloc, '/');
            try out.appendSlice(alloc, p);
        }
        _ = &is_abs;
        return try out.toOwnedSlice(alloc);
    }

    fn joinDirAndRel(alloc: std.mem.Allocator, dir: []const u8, rel: []const u8) ![]const u8 {
        if (dir.len == 0 or std.mem.eql(u8, dir, ".")) {
            return try normalizePath(alloc, rel);
        }
        const joined = try std.fmt.allocPrint(alloc, "{s}/{s}", .{ dir, rel });
        return try normalizePath(alloc, joined);
    }

    fn stripExtension(p: []const u8) []const u8 {
        if (std.mem.endsWith(u8, p, ".aethel") and p.len > 7) {
            return p[0 .. p.len - 7];
        }
        return p;
    }

    fn deriveModuleKey(self: *Loader, norm_path: []const u8, explicit_key: ?[]const u8) ![]const u8 {
        if (explicit_key) |k| return k;
        if (self.entry_dir.len > 0 and !std.mem.eql(u8, self.entry_dir, ".")) {
            const prefix = try std.fmt.allocPrint(self.alloc, "{s}/", .{self.entry_dir});
            if (std.mem.startsWith(u8, norm_path, prefix)) {
                return stripExtension(norm_path[prefix.len..]);
            }
        }
        return stripExtension(norm_path);
    }

    fn isBuiltinVirtualModule(imp_key: []const u8) bool {
        return std.mem.eql(u8, imp_key, "io") or
            std.mem.startsWith(u8, imp_key, "aethel/");
    }

    fn loadSourceBuffer(
        self: *Loader,
        norm_path: []const u8,
        explicit_key: ?[]const u8,
        src: [:0]const u8,
    ) std.mem.Allocator.Error!?usize {
        if (self.findLoadedByPath(norm_path)) |existing| {
            return existing;
        }
        if (self.isVisiting(norm_path)) {
            return null;
        }

        try self.visiting.append(self.alloc, norm_path);
        defer _ = self.visiting.pop();

        var tree = try parser.parse(self.alloc, src);
        defer tree.deinit();

        const cur_dir = std.fs.path.dirname(norm_path) orelse "";

        for (tree.module.decls) |decl| {
            if (decl.kind != .import_decl) continue;
            const imp = decl.kind.import_decl;
            if (imp.path.len == 0) continue;

            var key_buf: std.ArrayList(u8) = .empty;
            for (imp.path, 0..) |seg, i| {
                if (i > 0) try key_buf.append(self.alloc, '/');
                try key_buf.appendSlice(self.alloc, seg.slice(src));
            }
            const imp_key = try key_buf.toOwnedSlice(self.alloc);
            const rel_file = try std.fmt.allocPrint(self.alloc, "{s}.aethel", .{imp_key});

            if (self.memory_files != null) {
                if (self.findMemoryFile(imp_key)) |mf| {
                    if (self.isVisiting(mf.path)) {
                        const msg = try std.fmt.allocPrint(self.alloc, "circular import detected for module '{s}'", .{imp_key});
                        try self.errors.append(self.alloc, .{ .path = norm_path, .source = src, .span = decl.span, .message = msg });
                        continue;
                    }
                    _ = try self.loadFile(mf.path, mf.module_key);
                    continue;
                }
                const cand1 = try joinDirAndRel(self.alloc, cur_dir, rel_file);
                if (self.findMemoryFile(cand1)) |mf| {
                    if (self.isVisiting(mf.path)) {
                        const msg = try std.fmt.allocPrint(self.alloc, "circular import detected for module '{s}'", .{imp_key});
                        try self.errors.append(self.alloc, .{ .path = norm_path, .source = src, .span = decl.span, .message = msg });
                        continue;
                    }
                    _ = try self.loadFile(mf.path, mf.module_key);
                    continue;
                }
                if (stdlib.lookup(imp_key)) |std_src| {
                    const vpath = try std.fmt.allocPrint(self.alloc, "<std>/{s}", .{imp_key});
                    _ = try self.loadSourceBuffer(vpath, imp_key, std_src);
                    continue;
                }
                if (isBuiltinVirtualModule(imp_key)) continue;
                const msg = try std.fmt.allocPrint(self.alloc, "imported module '{s}' not found", .{imp_key});
                try self.errors.append(self.alloc, .{ .path = norm_path, .source = src, .span = decl.span, .message = msg });
                continue;
            }

            // Filesystem lookup: first relative to the importing file's directory, then relative to entry_dir.
            const cand_local = try joinDirAndRel(self.alloc, cur_dir, rel_file);
            const cand_entry = try joinDirAndRel(self.alloc, self.entry_dir, rel_file);

            var chosen: ?[]const u8 = null;
            var chosen_key: []const u8 = imp_key;
            if (self.readSource(cand_local) != null or self.findLoadedByPath(cand_local) != null or self.isVisiting(cand_local)) {
                chosen = cand_local;
                chosen_key = try self.deriveModuleKey(cand_local, null);
            } else if (!std.mem.eql(u8, cand_entry, cand_local) and
                (self.readSource(cand_entry) != null or self.findLoadedByPath(cand_entry) != null or self.isVisiting(cand_entry)))
            {
                chosen = cand_entry;
                chosen_key = imp_key;
            }

            if (chosen) |target_path| {
                if (self.isVisiting(target_path)) {
                    const msg = try std.fmt.allocPrint(self.alloc, "circular import detected for module '{s}'", .{imp_key});
                    try self.errors.append(self.alloc, .{ .path = norm_path, .source = src, .span = decl.span, .message = msg });
                    continue;
                }
                _ = try self.loadFile(target_path, chosen_key);
            } else if (stdlib.lookup(imp_key)) |std_src| {
                const vpath = try std.fmt.allocPrint(self.alloc, "<std>/{s}", .{imp_key});
                _ = try self.loadSourceBuffer(vpath, imp_key, std_src);
            } else {
                if (isBuiltinVirtualModule(imp_key)) continue;
                const msg = try std.fmt.allocPrint(self.alloc, "imported module file '{s}' not found", .{cand_entry});
                try self.errors.append(self.alloc, .{ .path = norm_path, .source = src, .span = decl.span, .message = msg });
            }
        }

        const mod_id = self.loaded.items.len;
        const mkey = try self.deriveModuleKey(norm_path, explicit_key);
        try self.loaded.append(self.alloc, .{
            .path = norm_path,
            .module_key = mkey,
            .source = src,
            .module_id = mod_id,
        });
        return mod_id;
    }

    fn loadFile(self: *Loader, norm_path: []const u8, explicit_key: ?[]const u8) std.mem.Allocator.Error!?usize {
        if (self.findLoadedByPath(norm_path)) |existing| {
            return existing;
        }
        if (self.isVisiting(norm_path)) {
            return null;
        }
        const src = self.readSource(norm_path) orelse return null;
        return try self.loadSourceBuffer(norm_path, explicit_key, src);
    }

    fn buildLoadedProgram(
        self: *Loader,
        arena: std.heap.ArenaAllocator,
        entry_module_id: usize,
        extra_files: []const struct { path: []const u8, source: [:0]const u8, module_id: usize, module_key: []const u8 },
    ) !LoadedProgram {
        var total_len: usize = 0;
        const total_count = self.loaded.items.len + extra_files.len;
        for (self.loaded.items, 0..) |lf, i| {
            if (i > 0) total_len += 1;
            total_len += lf.source.len;
        }
        for (extra_files, 0..) |ef, ei| {
            if (self.loaded.items.len > 0 or ei > 0) total_len += 1;
            total_len += ef.source.len;
        }

        const combined = try self.alloc.allocSentinel(u8, total_len, 0);
        const slices = try self.alloc.alloc(SourceSlice, total_count);

        var cursor: usize = 0;
        for (self.loaded.items, 0..) |lf, i| {
            if (i > 0) {
                combined[cursor] = '\n';
                cursor += 1;
            }
            const start = cursor;
            @memcpy(combined[cursor .. cursor + lf.source.len], lf.source);
            cursor += lf.source.len;
            slices[i] = .{
                .module_id = lf.module_id,
                .path = lf.path,
                .module_key = lf.module_key,
                .start = start,
                .end = cursor,
                .source = lf.source,
            };
        }
        for (extra_files, 0..) |ef, ei| {
            if (self.loaded.items.len > 0 or ei > 0) {
                combined[cursor] = '\n';
                cursor += 1;
            }
            const start = cursor;
            @memcpy(combined[cursor .. cursor + ef.source.len], ef.source);
            cursor += ef.source.len;
            slices[self.loaded.items.len + ei] = .{
                .module_id = ef.module_id,
                .path = ef.path,
                .module_key = ef.module_key,
                .start = start,
                .end = cursor,
                .source = ef.source,
            };
        }

        return .{
            .arena = arena,
            .combined_source = combined,
            .slices = slices,
            .entry_module_id = entry_module_id,
            .errors = try self.errors.toOwnedSlice(self.alloc),
        };
    }
};

/// Recursively load `entry_path`, all transitive `import` dependencies, and an optional
/// companion laws file into one concatenated source buffer with exact slice offsets.
pub fn loadProgram(
    allocator: std.mem.Allocator,
    io: Io,
    entry_path: []const u8,
    extra_laws_path: ?[]const u8,
) !LoadedProgram {
    var arena = std.heap.ArenaAllocator.init(allocator);
    errdefer arena.deinit();
    const alloc = arena.allocator();

    const norm_entry = try Loader.normalizePath(alloc, entry_path);
    const raw_dir = std.fs.path.dirname(norm_entry) orelse "";
    const norm_entry_dir = if (raw_dir.len > 0) try Loader.normalizePath(alloc, raw_dir) else "";

    var loader = Loader{
        .alloc = alloc,
        .io = io,
        .memory_files = null,
        .entry_dir = norm_entry_dir,
    };

    const entry_src = loader.readSource(norm_entry) orelse loader.readSource(entry_path) orelse {
        const msg = try std.fmt.allocPrint(alloc, "failed to read entry module '{s}'", .{entry_path});
        try loader.errors.append(alloc, .{
            .path = entry_path,
            .source = "",
            .span = .{ .start = 0, .end = 0 },
            .message = msg,
        });
        return .{
            .arena = arena,
            .combined_source = try Loader.dupeSentinelZ(alloc, ""),
            .slices = &.{},
            .entry_module_id = 0,
            .errors = try loader.errors.toOwnedSlice(alloc),
        };
    };
    _ = entry_src;

    const entry_key = Loader.stripExtension(std.fs.path.basename(norm_entry));
    const entry_id = (try loader.loadFile(norm_entry, entry_key)) orelse 0;

    if (extra_laws_path) |lp| {
        const norm_laws = try Loader.normalizePath(alloc, lp);
        if (loader.readSource(norm_laws) orelse loader.readSource(lp)) |laws_src| {
            return try loader.buildLoadedProgram(arena, entry_id, &.{.{
                .path = norm_laws,
                .source = laws_src,
                .module_id = entry_id,
                .module_key = entry_key,
            }});
        } else {
            const msg = try std.fmt.allocPrint(alloc, "failed to read companion laws file '{s}'", .{lp});
            try loader.errors.append(alloc, .{
                .path = lp,
                .source = "",
                .span = .{ .start = 0, .end = 0 },
                .message = msg,
            });
        }
    }

    return try loader.buildLoadedProgram(arena, entry_id, &.{});
}

/// Load a multi-file program from in-memory modules (used by unit tests).
pub fn loadFromMemory(
    allocator: std.mem.Allocator,
    entry_key: []const u8,
    files: []const MemoryFile,
) !LoadedProgram {
    var arena = std.heap.ArenaAllocator.init(allocator);
    errdefer arena.deinit();
    const alloc = arena.allocator();

    var loader = Loader{
        .alloc = alloc,
        .io = null,
        .memory_files = files,
        .entry_dir = "",
    };

    const entry_mf = loader.findMemoryFile(entry_key) orelse {
        const msg = try std.fmt.allocPrint(alloc, "entry module '{s}' not found", .{entry_key});
        try loader.errors.append(alloc, .{
            .path = entry_key,
            .source = "",
            .span = .{ .start = 0, .end = 0 },
            .message = msg,
        });
        return .{
            .arena = arena,
            .combined_source = try Loader.dupeSentinelZ(alloc, ""),
            .slices = &.{},
            .entry_module_id = 0,
            .errors = try loader.errors.toOwnedSlice(alloc),
        };
    };

    const entry_id = (try loader.loadFile(entry_mf.path, entry_mf.module_key)) orelse 0;
    return try loader.buildLoadedProgram(arena, entry_id, &.{});
}
