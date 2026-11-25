const std = @import("std");
const Io = std.Io;

pub const NativeDepSpec = struct {
    name: []const u8,
    raw_rhs: []const u8,
};

pub const RustDepSpec = struct {
    name: []const u8,
    version: ?[]const u8 = null,
    path: ?[]const u8 = null,
    default_features: bool = true,
    features: []const []const u8 = &.{},
};

pub const ProjectManifest = struct {
    pkg_name: []const u8,
    pkg_version: []const u8 = "0.1.0",
    entry: []const u8 = "src/main.aethel",
    rust_edition: []const u8 = "2021",
    rust_bridge: ?[]const u8 = null,
    native_deps: []const NativeDepSpec = &.{},
    rust_deps: []const RustDepSpec = &.{},
};

pub const ManifestError = error{
    InvalidManifest,
    InvalidCrateName,
    MissingPackageName,
    DuplicateRustDependency,
    MissingDependencySource,
} || std.mem.Allocator.Error;

pub fn isValidCrateIdent(s: []const u8) bool {
    if (s.len == 0) return false;
    if (s[0] < 'a' or s[0] > 'z') return false;
    for (s[1..]) |c| {
        const ok = (c >= 'a' and c <= 'z') or
            (c >= '0' and c <= '9') or
            c == '_' or c == '-';
        if (!ok) return false;
    }
    return true;
}

pub fn cratesMatch(a: []const u8, b: []const u8) bool {
    if (a.len != b.len) return false;
    for (a, b) |ca, cb| {
        const na = if (ca == '-') @as(u8, '_') else ca;
        const nb = if (cb == '-') @as(u8, '_') else cb;
        if (na != nb) return false;
    }
    return true;
}

pub fn normalizeCrateIdentAlloc(alloc: std.mem.Allocator, s: []const u8) ![]u8 {
    const buf = try alloc.dupe(u8, s);
    for (buf) |*c| {
        if (c.* == '-') c.* = '_';
    }
    return buf;
}

const Section = enum {
    none,
    package,
    dependencies,
    rust,
    rust_dependencies,
};

fn stripInlineComment(raw: []const u8) []const u8 {
    var in_str = false;
    var quote: u8 = 0;
    var escaped = false;
    for (raw, 0..) |c, i| {
        if (escaped) {
            escaped = false;
            continue;
        }
        if (in_str) {
            if (c == '\\') {
                escaped = true;
            } else if (c == quote) {
                in_str = false;
            }
            continue;
        }
        if (c == '"' or c == '\'') {
            in_str = true;
            quote = c;
            continue;
        }
        if (c == '#') return std.mem.trim(u8, raw[0..i], " \t\r");
    }
    return std.mem.trim(u8, raw, " \t\r");
}

fn unquoteTomlString(alloc: std.mem.Allocator, raw: []const u8) ManifestError![]const u8 {
    const trimmed = std.mem.trim(u8, raw, " \t\r");
    if (trimmed.len < 2) return error.InvalidManifest;
    if (trimmed[0] == '\'' and trimmed[trimmed.len - 1] == '\'') {
        return try alloc.dupe(u8, trimmed[1 .. trimmed.len - 1]);
    }
    if (trimmed[0] != '"' or trimmed[trimmed.len - 1] != '"') {
        return error.InvalidManifest;
    }
    const inner = trimmed[1 .. trimmed.len - 1];
    var out: std.ArrayList(u8) = .empty;
    var i: usize = 0;
    while (i < inner.len) : (i += 1) {
        if (inner[i] == '\\' and i + 1 < inner.len) {
            i += 1;
            switch (inner[i]) {
                'n' => try out.append(alloc, '\n'),
                'r' => try out.append(alloc, '\r'),
                't' => try out.append(alloc, '\t'),
                '\\' => try out.append(alloc, '\\'),
                '"' => try out.append(alloc, '"'),
                else => try out.append(alloc, inner[i]),
            }
        } else {
            try out.append(alloc, inner[i]);
        }
    }
    return try out.toOwnedSlice(alloc);
}

fn findTopLevelChar(s: []const u8, needle: u8) ?usize {
    var in_str = false;
    var quote: u8 = 0;
    var escaped = false;
    var depth_brace: usize = 0;
    var depth_bracket: usize = 0;
    for (s, 0..) |c, i| {
        if (escaped) {
            escaped = false;
            continue;
        }
        if (in_str) {
            if (c == '\\') {
                escaped = true;
            } else if (c == quote) {
                in_str = false;
            }
            continue;
        }
        if (c == '"' or c == '\'') {
            in_str = true;
            quote = c;
            continue;
        }
        if (c == '{') depth_brace += 1 else if (c == '}' and depth_brace > 0) depth_brace -= 1;
        if (c == '[') depth_bracket += 1 else if (c == ']' and depth_bracket > 0) depth_bracket -= 1;
        if (c == needle and depth_brace == 0 and depth_bracket == 0) return i;
    }
    return null;
}

fn splitTopLevelComma(alloc: std.mem.Allocator, inner: []const u8) ![][]const u8 {
    var items: std.ArrayList([]const u8) = .empty;
    var start: usize = 0;
    var in_str = false;
    var quote: u8 = 0;
    var escaped = false;
    var depth_brace: usize = 0;
    var depth_bracket: usize = 0;
    for (inner, 0..) |c, i| {
        if (escaped) {
            escaped = false;
            continue;
        }
        if (in_str) {
            if (c == '\\') {
                escaped = true;
            } else if (c == quote) {
                in_str = false;
            }
            continue;
        }
        if (c == '"' or c == '\'') {
            in_str = true;
            quote = c;
            continue;
        }
        if (c == '{') depth_brace += 1 else if (c == '}' and depth_brace > 0) depth_brace -= 1;
        if (c == '[') depth_bracket += 1 else if (c == ']' and depth_bracket > 0) depth_bracket -= 1;
        if (c == ',' and depth_brace == 0 and depth_bracket == 0) {
            const part = std.mem.trim(u8, inner[start..i], " \t\r");
            if (part.len > 0) try items.append(alloc, part);
            start = i + 1;
        }
    }
    const tail = std.mem.trim(u8, inner[start..], " \t\r");
    if (tail.len > 0) try items.append(alloc, tail);
    return try items.toOwnedSlice(alloc);
}

fn parseStringArray(alloc: std.mem.Allocator, raw: []const u8) ManifestError![]const []const u8 {
    const trimmed = std.mem.trim(u8, raw, " \t\r");
    if (trimmed.len < 2 or trimmed[0] != '[' or trimmed[trimmed.len - 1] != ']') {
        return error.InvalidManifest;
    }
    const parts = try splitTopLevelComma(alloc, trimmed[1 .. trimmed.len - 1]);
    const out = try alloc.alloc([]const u8, parts.len);
    for (parts, 0..) |p, idx| {
        out[idx] = try unquoteTomlString(alloc, p);
    }
    return out;
}

fn parseRustDepValue(alloc: std.mem.Allocator, name: []const u8, rhs: []const u8) ManifestError!RustDepSpec {
    const trimmed = std.mem.trim(u8, rhs, " \t\r");
    if (trimmed.len == 0) return error.InvalidManifest;
    if (trimmed[0] == '"' or trimmed[0] == '\'') {
        const ver = try unquoteTomlString(alloc, trimmed);
        return .{ .name = name, .version = ver };
    }
    if (trimmed[0] == '{' and trimmed[trimmed.len - 1] == '}') {
        var dep = RustDepSpec{ .name = name };
        const fields = try splitTopLevelComma(alloc, trimmed[1 .. trimmed.len - 1]);
        for (fields) |fld| {
            const eq = findTopLevelChar(fld, '=') orelse return error.InvalidManifest;
            const fk = std.mem.trim(u8, fld[0..eq], " \t\r");
            const fv = std.mem.trim(u8, fld[eq + 1 ..], " \t\r");
            if (std.mem.eql(u8, fk, "version")) {
                dep.version = try unquoteTomlString(alloc, fv);
            } else if (std.mem.eql(u8, fk, "path")) {
                dep.path = try unquoteTomlString(alloc, fv);
            } else if (std.mem.eql(u8, fk, "default-features") or std.mem.eql(u8, fk, "default_features")) {
                if (std.mem.eql(u8, fv, "true")) {
                    dep.default_features = true;
                } else if (std.mem.eql(u8, fv, "false")) {
                    dep.default_features = false;
                } else {
                    return error.InvalidManifest;
                }
            } else if (std.mem.eql(u8, fk, "features")) {
                dep.features = try parseStringArray(alloc, fv);
            }
        }
        if (dep.version == null and dep.path == null) return error.MissingDependencySource;
        return dep;
    }
    return error.InvalidManifest;
}

pub fn parseManifest(alloc: std.mem.Allocator, source: []const u8) ManifestError!ProjectManifest {
    var pkg_name: ?[]const u8 = null;
    var pkg_version: []const u8 = "0.1.0";
    var entry: []const u8 = "src/main.aethel";
    var rust_edition: []const u8 = "2021";
    var rust_bridge: ?[]const u8 = null;
    var native_deps: std.ArrayList(NativeDepSpec) = .empty;
    var rust_deps: std.ArrayList(RustDepSpec) = .empty;

    var sec: Section = .none;
    var line_it = std.mem.splitScalar(u8, source, '\n');
    while (line_it.next()) |raw_line| {
        const line = stripInlineComment(raw_line);
        if (line.len == 0) continue;
        if (line[0] == '[' and line[line.len - 1] == ']') {
            const header = std.mem.trim(u8, line[1 .. line.len - 1], " \t\r");
            if (std.mem.eql(u8, header, "package")) {
                sec = .package;
            } else if (std.mem.eql(u8, header, "dependencies")) {
                sec = .dependencies;
            } else if (std.mem.eql(u8, header, "rust")) {
                sec = .rust;
            } else if (std.mem.eql(u8, header, "rust-dependencies") or std.mem.eql(u8, header, "rust.dependencies")) {
                sec = .rust_dependencies;
            } else {
                sec = .none;
            }
            continue;
        }

        const eq = findTopLevelChar(line, '=') orelse return error.InvalidManifest;
        const key_raw = std.mem.trim(u8, line[0..eq], " \t\r");
        const rhs = std.mem.trim(u8, line[eq + 1 ..], " \t\r");
        const key = if (key_raw.len >= 2 and (key_raw[0] == '"' or key_raw[0] == '\''))
            try unquoteTomlString(alloc, key_raw)
        else
            try alloc.dupe(u8, key_raw);

        switch (sec) {
            .package => {
                if (std.mem.eql(u8, key, "name")) {
                    pkg_name = try unquoteTomlString(alloc, rhs);
                } else if (std.mem.eql(u8, key, "version")) {
                    pkg_version = try unquoteTomlString(alloc, rhs);
                } else if (std.mem.eql(u8, key, "entry")) {
                    entry = try unquoteTomlString(alloc, rhs);
                }
            },
            .dependencies => {
                try native_deps.append(alloc, .{
                    .name = key,
                    .raw_rhs = try alloc.dupe(u8, rhs),
                });
            },
            .rust => {
                if (std.mem.eql(u8, key, "edition")) {
                    rust_edition = try unquoteTomlString(alloc, rhs);
                } else if (std.mem.eql(u8, key, "bridge")) {
                    rust_bridge = try unquoteTomlString(alloc, rhs);
                }
            },
            .rust_dependencies => {
                if (!isValidCrateIdent(key)) return error.InvalidCrateName;
                for (rust_deps.items) |prev| {
                    if (cratesMatch(prev.name, key)) return error.DuplicateRustDependency;
                }
                const dep = try parseRustDepValue(alloc, key, rhs);
                try rust_deps.append(alloc, dep);
            },
            .none => {},
        }
    }

    const name = pkg_name orelse return error.MissingPackageName;
    if (!isValidCrateIdent(name)) return error.InvalidCrateName;
    if (entry.len == 0) return error.InvalidManifest;

    return .{
        .pkg_name = name,
        .pkg_version = pkg_version,
        .entry = entry,
        .rust_edition = rust_edition,
        .rust_bridge = rust_bridge,
        .native_deps = try native_deps.toOwnedSlice(alloc),
        .rust_deps = try rust_deps.toOwnedSlice(alloc),
    };
}

fn writeTomlEscapedString(writer: anytype, s: []const u8) !void {
    try writer.writeByte('"');
    for (s) |c| {
        switch (c) {
            '\\' => try writer.writeAll("\\\\"),
            '"' => try writer.writeAll("\\\""),
            '\n' => try writer.writeAll("\\n"),
            '\r' => try writer.writeAll("\\r"),
            '\t' => try writer.writeAll("\\t"),
            else => try writer.writeByte(c),
        }
    }
    try writer.writeByte('"');
}

pub fn renderManifest(alloc: std.mem.Allocator, m: *const ProjectManifest) ![]u8 {
    var out: Io.Writer.Allocating = .init(alloc);
    const w = &out.writer;

    try w.writeAll("[package]\n");
    try w.writeAll("name = ");
    try writeTomlEscapedString(w, m.pkg_name);
    try w.writeByte('\n');
    try w.writeAll("version = ");
    try writeTomlEscapedString(w, m.pkg_version);
    try w.writeByte('\n');
    try w.writeAll("entry = ");
    try writeTomlEscapedString(w, m.entry);
    try w.writeByte('\n');

    try w.writeAll("\n[dependencies]\n");
    for (m.native_deps) |nd| {
        try w.print("{s} = {s}\n", .{ nd.name, nd.raw_rhs });
    }

    if (!std.mem.eql(u8, m.rust_edition, "2021") or m.rust_bridge != null) {
        try w.writeAll("\n[rust]\n");
        try w.writeAll("edition = ");
        try writeTomlEscapedString(w, m.rust_edition);
        try w.writeByte('\n');
        if (m.rust_bridge) |rb| {
            try w.writeAll("bridge = ");
            try writeTomlEscapedString(w, rb);
            try w.writeByte('\n');
        }
    }

    try w.writeAll("\n[rust-dependencies]\n");
    for (m.rust_deps) |rd| {
        try renderRustDepLine(w, rd);
    }

    return try alloc.dupe(u8, out.written());
}

pub fn renderRustDepLine(w: anytype, rd: RustDepSpec) !void {
    try w.print("{s} = ", .{rd.name});
    if (rd.path == null and rd.default_features and rd.features.len == 0) {
        try writeTomlEscapedString(w, rd.version orelse "*");
        try w.writeByte('\n');
        return;
    }
    try w.writeAll("{ ");
    var first = true;
    if (rd.version) |v| {
        try w.writeAll("version = ");
        try writeTomlEscapedString(w, v);
        first = false;
    }
    if (rd.path) |p| {
        if (!first) try w.writeAll(", ");
        try w.writeAll("path = ");
        try writeTomlEscapedString(w, p);
        first = false;
    }
    if (!rd.default_features) {
        if (!first) try w.writeAll(", ");
        try w.writeAll("default-features = false");
        first = false;
    }
    if (rd.features.len > 0) {
        if (!first) try w.writeAll(", ");
        try w.writeAll("features = [");
        for (rd.features, 0..) |f, fi| {
            if (fi > 0) try w.writeAll(", ");
            try writeTomlEscapedString(w, f);
        }
        try w.writeByte(']');
    }
    try w.writeAll(" }\n");
}

pub fn parseAddCrateSpec(spec: []const u8) struct { name: []const u8, version: ?[]const u8 } {
    if (std.mem.indexOfScalar(u8, spec, '@')) |idx| {
        return .{
            .name = spec[0..idx],
            .version = if (idx + 1 < spec.len) spec[idx + 1 ..] else null,
        };
    }
    return .{ .name = spec, .version = null };
}

pub fn upsertRustDependency(
    alloc: std.mem.Allocator,
    existing: *const ProjectManifest,
    dep: RustDepSpec,
) ManifestError!ProjectManifest {
    if (!isValidCrateIdent(dep.name)) return error.InvalidCrateName;
    if (dep.version == null and dep.path == null) return error.MissingDependencySource;

    var list: std.ArrayList(RustDepSpec) = .empty;
    var replaced = false;
    for (existing.rust_deps) |prev| {
        if (cratesMatch(prev.name, dep.name)) {
            if (!replaced) {
                try list.append(alloc, dep);
                replaced = true;
            }
        } else {
            try list.append(alloc, prev);
        }
    }
    if (!replaced) {
        try list.append(alloc, dep);
    }

    var updated = existing.*;
    updated.rust_deps = try list.toOwnedSlice(alloc);
    return updated;
}

pub fn resolveFromDir(alloc: std.mem.Allocator, base_dir: []const u8, rel_or_abs: []const u8) ![]const u8 {
    if (rel_or_abs.len > 0 and rel_or_abs[0] == '/') {
        return try alloc.dupe(u8, rel_or_abs);
    }
    if (base_dir.len == 0 or std.mem.eql(u8, base_dir, ".")) {
        return try alloc.dupe(u8, rel_or_abs);
    }
    return try std.fmt.allocPrint(alloc, "{s}/{s}", .{ std.mem.trimEnd(u8, base_dir, "/"), rel_or_abs });
}

fn fileExists(io: Io, path: []const u8) bool {
    Io.Dir.cwd().access(io, path, .{}) catch return false;
    return true;
}

pub fn isDirectory(io: Io, path: []const u8) bool {
    var d = Io.Dir.cwd().openDir(io, path, .{}) catch return false;
    d.close(io);
    return true;
}

pub fn discoverManifestPath(io: Io, alloc: std.mem.Allocator, start_path: ?[]const u8) !?[]const u8 {
    if (start_path) |sp| {
        if (std.mem.eql(u8, std.fs.path.basename(sp), "aethel.toml") and fileExists(io, sp)) {
            return try alloc.dupe(u8, sp);
        }
        if (isDirectory(io, sp)) {
            const direct = try resolveFromDir(alloc, sp, "aethel.toml");
            if (fileExists(io, direct)) return direct;
            return null;
        }
    }

    const start_dir_raw: []const u8 = if (start_path) |sp|
        (std.fs.path.dirname(sp) orelse ".")
    else
        ".";

    const abs_start = Io.Dir.cwd().realPathFileAlloc(io, start_dir_raw, alloc) catch {
        const direct = try resolveFromDir(alloc, start_dir_raw, "aethel.toml");
        if (fileExists(io, direct)) return direct;
        return null;
    };

    var cur: []const u8 = abs_start;
    while (true) {
        const cand = try resolveFromDir(alloc, cur, "aethel.toml");
        if (fileExists(io, cand)) return cand;
        const parent = std.fs.path.dirname(cur) orelse break;
        if (std.mem.eql(u8, parent, cur)) break;
        cur = parent;
    }
    return null;
}

pub fn normalizePkgName(alloc: std.mem.Allocator, raw: []const u8) ![]u8 {
    const base = std.fs.path.basename(std.mem.trimEnd(u8, raw, "/"));
    if (base.len == 0) return try alloc.dupe(u8, "aethel_app");
    var out: std.ArrayList(u8) = .empty;
    for (base, 0..) |c, idx| {
        if (c >= 'A' and c <= 'Z') {
            try out.append(alloc, c + ('a' - 'A'));
        } else if ((c >= 'a' and c <= 'z') or (c >= '0' and c <= '9') or c == '_' or c == '-') {
            if (idx == 0 and !((c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z'))) {
                try out.appendSlice(alloc, "app_");
            }
            try out.append(alloc, c);
        } else {
            try out.append(alloc, '_');
        }
    }
    return try out.toOwnedSlice(alloc);
}
