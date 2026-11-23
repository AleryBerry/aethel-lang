const std = @import("std");
const Io = std.Io;
const build_options = @import("build_options");
const aethel = @import("aethel");

pub fn main(init: std.process.Init) void {
    const io = init.io;
    const arena: std.mem.Allocator = init.arena.allocator();

    var stderr_buf: [4096]u8 = undefined;
    var stderr_writer: Io.File.Writer = .init(.stderr(), io, &stderr_buf);
    const stderr = &stderr_writer.interface;

    const exit_code = runCli(init, io, arena, stderr) catch |err| blk: {
        stderr.print("fatal: compiler internal error ({s})\n", .{@errorName(err)}) catch {};
        stderr.flush() catch {};
        break :blk @as(u8, 1);
    };
    if (exit_code != 0) {
        std.process.exit(exit_code);
    }
}

fn runCli(
    init: std.process.Init,
    io: Io,
    arena: std.mem.Allocator,
    stderr: *Io.Writer,
) !u8 {
    const args = try init.minimal.args.toSlice(arena);

    var stdout_buf: [4096]u8 = undefined;
    var stdout_writer: Io.File.Writer = .init(.stdout(), io, &stdout_buf);
    const stdout = &stdout_writer.interface;

    if (args.len <= 1 or std.mem.eql(u8, args[1], "--help") or std.mem.eql(u8, args[1], "-h")) {
        try printUsage(stdout);
        try stdout.flush();
        return 0;
    }

    if (std.mem.eql(u8, args[1], "lex")) {
        if (args.len != 3) {
            try stderr.print("usage: aethel lex <file.aethel>\n", .{});
            try stderr.flush();
            return 2;
        }
        const path = args[2];
        const source = readSourceFile(io, arena, path, stderr) orelse return 1;

        const tokens = try aethel.Lexer.tokenizeAll(arena, source);
        var error_count: usize = 0;
        for (tokens) |tok| {
            const lc = aethel.computeLineCol(source, tok.loc.start);
            const lexeme = tok.loc.slice(source);
            try stdout.print("{d}:{d} {s}", .{ lc.line, lc.column, @tagName(tok.tag) });
            if (tok.tag != .eof) {
                try stdout.print(" \"{f}\"", .{std.zig.fmtString(lexeme)});
            }
            try stdout.print("\n", .{});
            if (tok.tag.isError()) error_count += 1;
        }
        try stdout.flush();
        if (error_count > 0) {
            try stderr.print("lexer reported {d} error token(s)\n", .{error_count});
            try stderr.flush();
            return 1;
        }
        return 0;
    }

    if (std.mem.eql(u8, args[1], "parse")) {
        if (args.len != 3) {
            try stderr.print("usage: aethel parse <file.aethel>\n", .{});
            try stderr.flush();
            return 2;
        }
        const path = args[2];
        const source = readSourceFile(io, arena, path, stderr) orelse return 1;

        var tree = try aethel.parse(arena, source);
        defer tree.deinit();
        if (tree.hasErrors()) {
            for (tree.diagnostics) |diag| {
                try printCaretDiagnostic(stderr, path, source, diag.span, diag.message);
            }
            try stderr.flush();
            return 1;
        }

        try aethel.ast.formatAst(&tree, stdout);
        try stdout.flush();
        return 0;
    }

    if (std.mem.eql(u8, args[1], "check") or
        std.mem.eql(u8, args[1], "emit-mir") or
        std.mem.eql(u8, args[1], "emit-zig"))
    {
        const emit_mir = std.mem.eql(u8, args[1], "emit-mir");
        const emit_zig = std.mem.eql(u8, args[1], "emit-zig");
        if (args.len != 3) {
            try stderr.print("usage: aethel {s} <file.aethel>\n", .{args[1]});
            try stderr.flush();
            return 2;
        }
        const path = args[2];
        const source = readSourceFile(io, arena, path, stderr) orelse return 1;

        var tree = try aethel.parse(arena, source);
        defer tree.deinit();
        if (tree.hasErrors()) {
            for (tree.diagnostics) |diag| {
                try printCaretDiagnostic(stderr, path, source, diag.span, diag.message);
            }
            try stderr.flush();
            return 1;
        }

        var checked = try aethel.check(arena, &tree);
        defer checked.deinit();
        if (checked.hasErrors()) {
            for (checked.diagnostics) |diag| {
                try printCaretDiagnostic(stderr, path, source, diag.span, diag.message);
            }
            try stderr.flush();
            return 1;
        }

        if (emit_mir) {
            try aethel.emitMir(&checked, stdout);
            try stdout.flush();
            return 0;
        }
        if (emit_zig) {
            try aethel.emitZig(&tree, &checked, stdout);
            try stdout.flush();
            return 0;
        }

        try stdout.print("Aethel check passed: records={d}, adts={d}, collections={d}, functions={d}, laws={d}\n", .{
            checked.records.len,
            checked.adts.len,
            checked.collections.len,
            checked.functions.len,
            checked.laws.len,
        });
        for (checked.records) |rec| {
            try stdout.print("  record {s}: size={d} align={d} conflicts={d}\n", .{
                rec.name,
                rec.record_layout.size,
                rec.record_layout.alignment,
                rec.conflicts.len,
            });
        }
        for (checked.laws) |law| {
            try stdout.print("  law {s}: {s}\n", .{ law.name, @tagName(law.verdict) });
        }
        try stdout.flush();
        return 0;
    }

    if (std.mem.eql(u8, args[1], "build") or std.mem.eql(u8, args[1], "run")) {
        const is_run = std.mem.eql(u8, args[1], "run");
        return try handleBuildOrRun(io, arena, args[2..], is_run, stdout, stderr);
    }

    try stderr.print("unknown command '{s}'; run 'aethel --help'\n", .{args[1]});
    try stderr.flush();
    return 2;
}

const OptLevel = enum {
    debug,
    safe,
    fast,
    small,
};

fn handleBuildOrRun(
    io: Io,
    arena: std.mem.Allocator,
    rest: []const []const u8,
    is_run: bool,
    stdout: *Io.Writer,
    stderr: *Io.Writer,
) !u8 {
    var input_path: ?[]const u8 = null;
    var out_path_opt: ?[]const u8 = null;
    var opt_level: OptLevel = .debug;
    var keep_zig = false;

    var i: usize = 0;
    while (i < rest.len) : (i += 1) {
        const arg = rest[i];
        if (!is_run and std.mem.eql(u8, arg, "-o")) {
            i += 1;
            if (i >= rest.len) {
                try stderr.print("error: missing output path after '-o'\n", .{});
                try stderr.flush();
                return 2;
            }
            out_path_opt = rest[i];
        } else if (std.mem.eql(u8, arg, "-O")) {
            i += 1;
            if (i >= rest.len) {
                try stderr.print("error: missing optimization mode after '-O' (debug|safe|fast|small)\n", .{});
                try stderr.flush();
                return 2;
            }
            const m = rest[i];
            if (std.mem.eql(u8, m, "debug")) {
                opt_level = .debug;
            } else if (std.mem.eql(u8, m, "safe")) {
                opt_level = .safe;
            } else if (std.mem.eql(u8, m, "fast")) {
                opt_level = .fast;
            } else if (std.mem.eql(u8, m, "small")) {
                opt_level = .small;
            } else {
                try stderr.print("error: invalid -O mode '{s}' (expected debug, safe, fast, or small)\n", .{m});
                try stderr.flush();
                return 2;
            }
        } else if (std.mem.eql(u8, arg, "--keep-zig")) {
            keep_zig = true;
        } else if (std.mem.startsWith(u8, arg, "-")) {
            try stderr.print("error: unknown flag '{s}'\n", .{arg});
            try stderr.flush();
            return 2;
        } else if (input_path == null) {
            input_path = arg;
        } else {
            try stderr.print("error: unexpected argument '{s}'\n", .{arg});
            try stderr.flush();
            return 2;
        }
    }

    const path = input_path orelse {
        try stderr.print("usage: aethel {s} <file.aethel>{s} [-O debug|safe|fast|small] [--keep-zig]\n", .{
            if (is_run) "run" else "build",
            if (is_run) "" else " [-o <out>]",
        });
        try stderr.flush();
        return 2;
    };

    const source = readSourceFile(io, arena, path, stderr) orelse return 1;

    var tree = try aethel.parse(arena, source);
    defer tree.deinit();
    if (tree.hasErrors()) {
        for (tree.diagnostics) |diag| {
            try printCaretDiagnostic(stderr, path, source, diag.span, diag.message);
        }
        try stderr.flush();
        return 1;
    }

    var checked = try aethel.check(arena, &tree);
    defer checked.deinit();
    if (checked.hasErrors()) {
        for (checked.diagnostics) |diag| {
            try printCaretDiagnostic(stderr, path, source, diag.span, diag.message);
        }
        try stderr.flush();
        return 1;
    }

    var has_main = false;
    for (checked.functions) |f| {
        if (std.mem.eql(u8, f.name, "main")) {
            has_main = true;
            break;
        }
    }
    if (!has_main) {
        try stderr.print("{s}: error: no 'fn main()' entry point found in module\n", .{path});
        try stderr.flush();
        return 1;
    }

    var zig_buf: Io.Writer.Allocating = .init(arena);
    try aethel.emitZig(&tree, &checked, &zig_buf.writer);
    const zig_src = zig_buf.written();

    const base_name = std.fs.path.basename(path);
    const raw_stem = if (std.mem.endsWith(u8, base_name, ".aethel") and base_name.len > 7)
        base_name[0 .. base_name.len - 7]
    else if (base_name.len > 0)
        base_name
    else
        "aethel_prog";

    Io.Dir.cwd().createDirPath(io, ".aethel-build/cache") catch |err| {
        try stderr.print("error: failed to create .aethel-build directory: {s}\n", .{@errorName(err)});
        try stderr.flush();
        return 1;
    };

    const zig_path = try std.fmt.allocPrint(arena, ".aethel-build/{s}.zig", .{raw_stem});
    const out_path = out_path_opt orelse try std.fmt.allocPrint(arena, ".aethel-build/{s}", .{raw_stem});

    if (std.fs.path.dirname(out_path)) |parent| {
        if (parent.len > 0) {
            Io.Dir.cwd().createDirPath(io, parent) catch |err| {
                try stderr.print("error: failed to create output directory '{s}': {s}\n", .{ parent, @errorName(err) });
                try stderr.flush();
                return 1;
            };
        }
    }

    Io.Dir.cwd().writeFile(io, .{ .sub_path = zig_path, .data = zig_src }) catch |err| {
        try stderr.print("error: failed to write generated Zig source '{s}': {s}\n", .{ zig_path, @errorName(err) });
        try stderr.flush();
        return 1;
    };
    defer if (!keep_zig) {
        Io.Dir.cwd().deleteFile(io, zig_path) catch {};
    };

    const emit_bin_flag = try std.fmt.allocPrint(arena, "-femit-bin={s}", .{out_path});
    var argv_list: std.ArrayList([]const u8) = .empty;
    try argv_list.appendSlice(arena, &.{
        build_options.zig_exe,
        "build-exe",
        zig_path,
        "-fno-llvm",
        "-fno-lld",
    });
    switch (opt_level) {
        .debug => {},
        .safe => try argv_list.appendSlice(arena, &.{ "-O", "ReleaseSafe" }),
        .fast => try argv_list.appendSlice(arena, &.{ "-O", "ReleaseFast" }),
        .small => try argv_list.appendSlice(arena, &.{ "-O", "ReleaseSmall" }),
    }
    try argv_list.appendSlice(arena, &.{
        emit_bin_flag,
        "--cache-dir",
        ".aethel-build/cache",
    });

    const build_res = std.process.run(arena, io, .{ .argv = argv_list.items }) catch |err| {
        try stderr.print("error: failed to invoke Zig compiler '{s}': {s}\n", .{ build_options.zig_exe, @errorName(err) });
        try stderr.flush();
        return 1;
    };
    if (!build_res.term.success()) {
        try stderr.print("error: Zig built-in compiler failed to build '{s}' ({f})\n{s}\n", .{
            path,
            build_res.term,
            build_res.stderr,
        });
        try stderr.flush();
        return 1;
    }

    if (!is_run) {
        try stdout.print("Built {s} (Zig built-in compiler, no LLVM)\n", .{out_path});
        try stdout.flush();
        return 0;
    }

    const exec_path = if (!std.mem.startsWith(u8, out_path, "/") and std.mem.indexOfScalar(u8, out_path, '/') == null)
        try std.fmt.allocPrint(arena, "./{s}", .{out_path})
    else
        out_path;

    var child = std.process.spawn(io, .{
        .argv = &.{exec_path},
        .stdin = .inherit,
        .stdout = .inherit,
        .stderr = .inherit,
    }) catch |err| {
        try stderr.print("error: failed to execute '{s}': {s}\n", .{ exec_path, @errorName(err) });
        try stderr.flush();
        return 1;
    };
    const term = child.wait(io) catch |err| {
        try stderr.print("error: failed waiting for '{s}': {s}\n", .{ exec_path, @errorName(err) });
        try stderr.flush();
        return 1;
    };
    return switch (term) {
        .exited => |code| code,
        else => 1,
    };
}

fn readSourceFile(
    io: Io,
    arena: std.mem.Allocator,
    path: []const u8,
    stderr: *Io.Writer,
) ?[:0]const u8 {
    return Io.Dir.cwd().readFileAllocOptions(
        io,
        path,
        arena,
        .limited(16 * 1024 * 1024),
        .of(u8),
        0,
    ) catch |err| {
        stderr.print("error: failed to read '{s}': {s}\n", .{ path, @errorName(err) }) catch {};
        stderr.flush() catch {};
        return null;
    };
}

fn printCaretDiagnostic(
    stderr: *Io.Writer,
    path: []const u8,
    source: [:0]const u8,
    span: aethel.ast.Span,
    message: []const u8,
) Io.Writer.Error!void {
    const lc = aethel.computeLineCol(source, span.start);
    const line_text = source[lc.line_start..lc.line_end];
    try stderr.print("{s}:{d}:{d}: error: {s}\n  {s}\n  ", .{
        path,
        lc.line,
        lc.column,
        message,
        line_text,
    });
    var col_i: usize = 1;
    while (col_i < lc.column) : (col_i += 1) {
        try stderr.writeByte(' ');
    }
    try stderr.writeAll("^\n");
}

fn printUsage(writer: *Io.Writer) Io.Writer.Error!void {
    try writer.print(
        \\Aethel compiler (Zig 0.17.0 built-in backend — no LLVM)
        \\
        \\Usage:
        \\  aethel --help
        \\  aethel lex <file.aethel>
        \\  aethel parse <file.aethel>
        \\  aethel check <file.aethel>
        \\  aethel emit-mir <file.aethel>
        \\  aethel emit-zig <file.aethel>
        \\  aethel build <file.aethel> [-o <out>] [-O debug|safe|fast|small] [--keep-zig]
        \\  aethel run <file.aethel> [-O debug|safe|fast|small] [--keep-zig]
        \\
    , .{});
}

test "main CLI module sanity check" {
    var tree = try aethel.parse(std.testing.allocator, "fn ok(x: u8) -> u8 { x }");
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());
    var checked = try aethel.check(std.testing.allocator, &tree);
    defer checked.deinit();
    try std.testing.expect(!checked.hasErrors());
}
