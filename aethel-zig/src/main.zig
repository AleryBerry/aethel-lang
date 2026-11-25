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

    if (std.mem.eql(u8, args[1], "new")) {
        return try handleNew(io, arena, args[2..], stdout, stderr);
    }

    if (std.mem.eql(u8, args[1], "add")) {
        return try handleAdd(io, arena, args[2..], stdout, stderr);
    }

    if (std.mem.eql(u8, args[1], "check") or
        std.mem.eql(u8, args[1], "emit-mir") or
        std.mem.eql(u8, args[1], "emit-zig") or
        std.mem.eql(u8, args[1], "emit-rust-adapter"))
    {
        const is_check = std.mem.eql(u8, args[1], "check");
        const emit_mir = std.mem.eql(u8, args[1], "emit-mir");
        const emit_zig = std.mem.eql(u8, args[1], "emit-zig");
        const emit_rust = std.mem.eql(u8, args[1], "emit-rust-adapter");
        var explain_layout = false;
        var path_opt: ?[]const u8 = null;
        for (args[2..]) |arg| {
            if (is_check and std.mem.eql(u8, arg, "--explain-layout")) {
                explain_layout = true;
            } else if (std.mem.startsWith(u8, arg, "--")) {
                try stderr.print("error: unknown flag '{s}'\n", .{arg});
                try stderr.flush();
                return 2;
            } else if (path_opt == null) {
                path_opt = arg;
            } else {
                const flag_hint = if (is_check) "[--explain-layout] " else "";
                try stderr.print("usage: aethel {s} {s}[<file.aethel|dir>]\n", .{ args[1], flag_hint });
                try stderr.flush();
                return 2;
            }
        }
        const resolved = (try resolveCliTarget(io, arena, path_opt, stderr)) orelse return 1;
        const path = resolved.entry_path;

        var loaded = try aethel.module_loader.loadProgram(arena, io, path, null);
        defer loaded.deinit();
        if (loaded.hasErrors()) {
            for (loaded.errors) |lerr| {
                try printLoadedError(stderr, lerr);
            }
            try stderr.flush();
            return 1;
        }

        var tree = try aethel.parse(arena, loaded.combined_source);
        defer tree.deinit();
        if (tree.hasErrors()) {
            for (tree.diagnostics) |diag| {
                try printLocatedCaretDiagnostic(stderr, loaded.slices, path, loaded.combined_source, diag.span, diag.message);
            }
            try stderr.flush();
            return 1;
        }

        const mod_infos = try slicesToModuleInfos(arena, loaded.slices);
        var checked = try aethel.checkWithModulesAndManifest(
            arena,
            &tree,
            mod_infos,
            loaded.entry_module_id,
            resolved.pkg_name,
            resolved.declared_crates,
        );
        defer checked.deinit();
        if (checked.hasErrors()) {
            for (checked.diagnostics) |diag| {
                try printLocatedCaretDiagnostic(stderr, loaded.slices, path, loaded.combined_source, diag.span, diag.message);
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
        if (emit_rust) {
            if (resolved.manifest != null) {
                var user_src: ?[]const u8 = null;
                if (resolved.user_rust_bridge) |bp| {
                    user_src = Io.Dir.cwd().readFileAllocOptions(io, bp, arena, .limited(16 * 1024 * 1024), .of(u8), 0) catch null;
                }
                try aethel.rust_ffi.emitCargoProjectAdapter(&tree, &checked, user_src, resolved.pkg_name, stdout);
            } else {
                try aethel.rust_ffi.emitRustAdapter(&tree, &checked, null, stdout);
            }
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
            if (explain_layout) {
                var naive_bytes: usize = 0;
                for (rec.record_layout.fields) |fp| {
                    naive_bytes += @max(@as(usize, 1), fp.size);
                }
                const saved_bytes: isize = @as(isize, @intCast(naive_bytes)) - @as(isize, @intCast(rec.record_layout.size));
                try stdout.print("    naive_size={d} saved={d}B", .{ naive_bytes, saved_bytes });
                if (rec.collection_layout) |cl| {
                    switch (cl) {
                        .aos => try stdout.writeAll(" collection=aos"),
                        .soa => try stdout.writeAll(" collection=soa"),
                        .aosoa => |w| try stdout.print(" collection=aosoa({d})", .{w}),
                    }
                } else {
                    try stdout.writeAll(" collection=scalar");
                }
                if (rec.auto_layout_decision) |dec| {
                    try stdout.print(" auto_policy(hot_ratio={d}%: {s})", .{ dec.hot_ratio_pct, dec.reason });
                }
                try stdout.writeAll("\n");
                for (rec.fields, 0..) |cf, fi| {
                    const fp = rec.record_layout.fields[fi];
                    const is_hot = fi < rec.hot_fields.len and rec.hot_fields[fi];
                    const temp_label: []const u8 = if (is_hot) "hot" else "cold";
                    if (fp.bit_offset) |boff| {
                        try stdout.print("    field {s}: bits={d} byte={d} bit={d} ({s}, ffd_packed)\n", .{
                            cf.name,
                            cf.bits,
                            fp.byte_offset,
                            boff,
                            temp_label,
                        });
                    } else {
                        try stdout.print("    field {s}: bits={d} byte={d} size={d} align={d} ({s}, addressable)\n", .{
                            cf.name,
                            cf.bits,
                            fp.byte_offset,
                            fp.size,
                            fp.alignment,
                            temp_label,
                        });
                    }
                }
            }
        }
        if (explain_layout) {
            for (checked.adts) |adt_def| {
                const mode_str: []const u8 = if (adt_def.adt_layout.tag_bits >= 1 and adt_def.adt_layout.max_payload_bits >= 1 and adt_def.adt_layout.total_bits <= 8)
                    "compact_packed_byte"
                else if (adt_def.adt_layout.max_payload_bits == 0)
                    "compact_enum"
                else
                    "tagged_union";
                try stdout.print("  adt {s}: tag_bits={d} max_payload_bits={d} total_bits={d} total_bytes={d} mode={s}\n", .{
                    adt_def.name,
                    adt_def.adt_layout.tag_bits,
                    adt_def.adt_layout.max_payload_bits,
                    adt_def.adt_layout.total_bits,
                    adt_def.adt_layout.total_bytes,
                    mode_str,
                });
            }
        }
        for (checked.laws) |law| {
            try stdout.print("  law {s}: {s}\n", .{ law.name, @tagName(law.verdict) });
        }
        try stdout.flush();
        return 0;
    }

    if (std.mem.eql(u8, args[1], "verify")) {
        return try handleVerify(io, arena, args[2..], stdout, stderr);
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

const BackendKind = enum {
    zig,
    llvm,
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
    var rust_path_opt: ?[]const u8 = null;
    var opt_level: OptLevel = .debug;
    var backend_opt: ?BackendKind = null;
    var keep_zig = false;
    var offline = false;
    var release_flag = false;

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
        } else if (std.mem.eql(u8, arg, "--rust")) {
            i += 1;
            if (i >= rest.len) {
                try stderr.print("error: missing Rust source path after '--rust'\n", .{});
                try stderr.flush();
                return 2;
            }
            rust_path_opt = rest[i];
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
        } else if (std.mem.eql(u8, arg, "--backend")) {
            i += 1;
            if (i >= rest.len) {
                try stderr.print("error: missing backend after '--backend' (zig|llvm)\n", .{});
                try stderr.flush();
                return 2;
            }
            const b = rest[i];
            if (std.mem.eql(u8, b, "zig")) {
                backend_opt = .zig;
            } else if (std.mem.eql(u8, b, "llvm")) {
                backend_opt = .llvm;
            } else {
                try stderr.print("error: invalid --backend '{s}' (expected zig or llvm)\n", .{b});
                try stderr.flush();
                return 2;
            }
        } else if (std.mem.eql(u8, arg, "--keep-zig")) {
            keep_zig = true;
        } else if (std.mem.eql(u8, arg, "--offline")) {
            offline = true;
        } else if (std.mem.eql(u8, arg, "--release")) {
            release_flag = true;
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

    const resolved = (try resolveCliTarget(io, arena, input_path, stderr)) orelse return 1;
    const path = resolved.entry_path;

    var loaded = try aethel.module_loader.loadProgram(arena, io, path, null);
    defer loaded.deinit();
    if (loaded.hasErrors()) {
        for (loaded.errors) |lerr| {
            try printLoadedError(stderr, lerr);
        }
        try stderr.flush();
        return 1;
    }

    var tree = try aethel.parse(arena, loaded.combined_source);
    defer tree.deinit();
    if (tree.hasErrors()) {
        for (tree.diagnostics) |diag| {
            try printLocatedCaretDiagnostic(stderr, loaded.slices, path, loaded.combined_source, diag.span, diag.message);
        }
        try stderr.flush();
        return 1;
    }

    const mod_infos = try slicesToModuleInfos(arena, loaded.slices);
    var checked = try aethel.checkWithModulesAndManifest(
        arena,
        &tree,
        mod_infos,
        loaded.entry_module_id,
        resolved.pkg_name,
        resolved.declared_crates,
    );
    defer checked.deinit();
    if (checked.hasErrors()) {
        for (checked.diagnostics) |diag| {
            try printLocatedCaretDiagnostic(stderr, loaded.slices, path, loaded.combined_source, diag.span, diag.message);
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
    const raw_stem = if (resolved.pkg_name) |pn|
        pn
    else if (std.mem.endsWith(u8, base_name, ".aethel") and base_name.len > 7)
        base_name[0 .. base_name.len - 7]
    else if (base_name.len > 0)
        base_name
    else
        "aethel_prog";

    const build_root = try aethel.manifest.resolveFromDir(arena, resolved.project_root, ".aethel-build");
    const cache_dir = try std.fmt.allocPrint(arena, "{s}/cache", .{build_root});
    Io.Dir.cwd().createDirPath(io, cache_dir) catch |err| {
        try stderr.print("error: failed to create .aethel-build directory: {s}\n", .{@errorName(err)});
        try stderr.flush();
        return 1;
    };

    const zig_path = try std.fmt.allocPrint(arena, "{s}/{s}.zig", .{ build_root, raw_stem });
    const out_path = out_path_opt orelse try std.fmt.allocPrint(arena, "{s}/{s}", .{ build_root, raw_stem });

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

    const backend: BackendKind = backend_opt orelse if (release_flag or opt_level != .debug) .llvm else .zig;
    const emit_bin_flag = try std.fmt.allocPrint(arena, "-femit-bin={s}", .{out_path});

    var rust_lib_opt: ?[]const u8 = null;
    var link_flags: []const []const u8 = &.{ "-lc", "-lgcc_s" };
    var cargo_pm_opt: ?*const aethel.manifest.ProjectManifest = null;
    var tried_cross_lto = false;

    if (rust_path_opt) |rp| {
        rust_lib_opt = (try aethel.rust_ffi.compileRustStaticlib(io, arena, &tree, &checked, rp, raw_stem, stderr)) orelse return 1;
    } else if (resolved.manifest) |*pm| {
        if (pm.rust_deps.len > 0 or resolved.user_rust_bridge != null) {
            cargo_pm_opt = pm;
            const cargo_release = release_flag or opt_level != .debug;
            const want_cross_lto = (backend == .llvm) and (release_flag or opt_level == .fast or opt_level == .small);
            if (want_cross_lto) {
                if (try aethel.rust_ffi.compileCargoProjectStaticlibOpts(
                    io,
                    arena,
                    &tree,
                    &checked,
                    resolved.project_root,
                    pm,
                    resolved.user_rust_bridge,
                    cargo_release,
                    offline,
                    .{ .use_cross_lto = true, .quiet_on_fail = true },
                    stderr,
                )) |cargo_out| {
                    rust_lib_opt = cargo_out.staticlib_path;
                    link_flags = cargo_out.link_flags;
                    tried_cross_lto = true;
                }
            }
            if (!tried_cross_lto) {
                const cargo_out = (try aethel.rust_ffi.compileCargoProjectStaticlibOpts(
                    io,
                    arena,
                    &tree,
                    &checked,
                    resolved.project_root,
                    pm,
                    resolved.user_rust_bridge,
                    cargo_release,
                    offline,
                    .{ .use_cross_lto = false, .quiet_on_fail = false },
                    stderr,
                )) orelse return 1;
                rust_lib_opt = cargo_out.staticlib_path;
                link_flags = cargo_out.link_flags;
            }
        }
    }

    var build_res = try runZigBuildExe(io, arena, zig_path, emit_bin_flag, cache_dir, opt_level, backend, release_flag, rust_lib_opt, link_flags, true, tried_cross_lto, stderr) orelse return 1;
    if (!build_res.term.success() and tried_cross_lto) {
        if (cargo_pm_opt) |pm| {
            // Fall back cleanly from Cross-Language ThinLTO bitcode to native staticlib `.a` linking
            // (preserving `#[inline(never)]` `noalias` SoA boundaries) when linker bitcode versions differ.
            const cargo_out = (try aethel.rust_ffi.compileCargoProjectStaticlibOpts(
                io,
                arena,
                &tree,
                &checked,
                resolved.project_root,
                pm,
                resolved.user_rust_bridge,
                release_flag or opt_level != .debug,
                offline,
                .{ .use_cross_lto = false, .quiet_on_fail = false },
                stderr,
            )) orelse return 1;
            rust_lib_opt = cargo_out.staticlib_path;
            link_flags = cargo_out.link_flags;
            build_res = try runZigBuildExe(io, arena, zig_path, emit_bin_flag, cache_dir, opt_level, backend, release_flag, rust_lib_opt, link_flags, true, false, stderr) orelse return 1;
        }
    }
    if (!build_res.term.success() and rust_lib_opt != null and backend == .zig) {
        // Retry without `-fno-lld` (still strictly `-fno-llvm`) for large external Cargo archives.
        build_res = try runZigBuildExe(io, arena, zig_path, emit_bin_flag, cache_dir, opt_level, backend, release_flag, rust_lib_opt, link_flags, false, false, stderr) orelse return 1;
    }
    if (!build_res.term.success()) {
        try stderr.print("error: Zig compiler failed to build '{s}' ({f})\n{s}\n", .{
            path,
            build_res.term,
            build_res.stderr,
        });
        try stderr.flush();
        return 1;
    }

    if (!is_run) {
        try stdout.print("Built {s} ({s})\n", .{
            out_path,
            if (backend == .llvm) "LLVM backend" else "Zig built-in compiler, no LLVM",
        });
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

fn handleVerify(
    io: Io,
    arena: std.mem.Allocator,
    rest: []const []const u8,
    stdout: *Io.Writer,
    stderr: *Io.Writer,
) !u8 {
    var input_path: ?[]const u8 = null;
    var explicit_laws: ?[]const u8 = null;
    var run_lean = true;

    var i: usize = 0;
    while (i < rest.len) : (i += 1) {
        const arg = rest[i];
        if (std.mem.eql(u8, arg, "--laws")) {
            i += 1;
            if (i >= rest.len) {
                try stderr.print("error: missing file path after '--laws'\n", .{});
                try stderr.flush();
                return 2;
            }
            explicit_laws = rest[i];
        } else if (std.mem.eql(u8, arg, "--lean")) {
            run_lean = true;
        } else if (std.mem.eql(u8, arg, "--no-lean")) {
            run_lean = false;
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

    const resolved = (try resolveCliTarget(io, arena, input_path, stderr)) orelse return 1;
    const path = resolved.entry_path;

    var companion_path: ?[]const u8 = null;
    if (explicit_laws) |lp| {
        companion_path = lp;
    } else {
        const bname = std.fs.path.basename(path);
        if (!std.mem.eql(u8, bname, "LAWS.aethel") and !std.mem.eql(u8, bname, "laws.aethel")) {
            const dir_opt = std.fs.path.dirname(path);
            const cands = [_][]const u8{ "LAWS.aethel", "laws.aethel" };
            for (cands) |cand_name| {
                const cand_path = if (dir_opt) |d|
                    if (d.len > 0) try std.fmt.allocPrint(arena, "{s}/{s}", .{ d, cand_name }) else cand_name
                else
                    cand_name;
                if (Io.Dir.cwd().readFileAllocOptions(
                    io,
                    cand_path,
                    arena,
                    .limited(16 * 1024 * 1024),
                    .of(u8),
                    0,
                )) |_| {
                    companion_path = cand_path;
                    break;
                } else |_| {}
            }
        }
    }

    var loaded = try aethel.module_loader.loadProgram(arena, io, path, companion_path);
    defer loaded.deinit();
    if (loaded.hasErrors()) {
        for (loaded.errors) |lerr| {
            try printLoadedError(stderr, lerr);
        }
        try stderr.flush();
        return 1;
    }

    var tree = try aethel.parse(arena, loaded.combined_source);
    defer tree.deinit();
    if (tree.hasErrors()) {
        for (tree.diagnostics) |diag| {
            try printLocatedCaretDiagnostic(stderr, loaded.slices, path, loaded.combined_source, diag.span, diag.message);
        }
        try stderr.flush();
        return 1;
    }

    const mod_infos = try slicesToModuleInfos(arena, loaded.slices);
    var checked = try aethel.checkWithModulesAndManifest(
        arena,
        &tree,
        mod_infos,
        loaded.entry_module_id,
        resolved.pkg_name,
        resolved.declared_crates,
    );
    defer checked.deinit();

    var has_non_law_error = false;
    for (checked.diagnostics) |diag| {
        if (diag.kind != .law_violation and diag.kind != .termination_error) {
            has_non_law_error = true;
            break;
        }
    }
    if (has_non_law_error) {
        for (checked.diagnostics) |diag| {
            try printLocatedCaretDiagnostic(stderr, loaded.slices, path, loaded.combined_source, diag.span, diag.message);
        }
        try stderr.flush();
        return 1;
    }

    var any_blocked = checked.hasErrors();
    var total_decreases_certs: usize = 0;
    for (checked.functions) |cf| {
        total_decreases_certs += cf.decreases_certs.len;
    }

    var lean_summary: ?[]const u8 = null;
    if (run_lean and !checked.hasErrors()) {
        var mir_buf: Io.Writer.Allocating = .init(arena);
        try aethel.emitMir(&checked, &mir_buf.writer);

        Io.Dir.cwd().createDirPath(io, ".aethel-build") catch |err| {
            try stderr.print("error: failed to create .aethel-build directory: {s}\n", .{@errorName(err)});
            try stderr.flush();
            return 1;
        };
        const stem = std.fs.path.basename(path);
        const mir_path = try std.fmt.allocPrint(arena, ".aethel-build/{s}.verify.mir", .{stem});
        Io.Dir.cwd().writeFile(io, .{ .sub_path = mir_path, .data = mir_buf.written() }) catch |err| {
            try stderr.print("error: failed to write MIR '{s}': {s}\n", .{ mir_path, @errorName(err) });
            try stderr.flush();
            return 1;
        };
        defer Io.Dir.cwd().deleteFile(io, mir_path) catch {};

        const checker_bin = try std.fmt.allocPrint(arena, "{s}/.lake/build/bin/aethel-check", .{build_options.lean_dir});
        const lean_res = std.process.run(arena, io, .{ .argv = &.{ checker_bin, mir_path } }) catch |err| {
            try stderr.print("error: failed to invoke Lean MIR validator '{s}': {s}\n", .{ checker_bin, @errorName(err) });
            try stderr.flush();
            return 1;
        };
        if (!lean_res.term.success()) {
            any_blocked = true;
            try stderr.print("error: Lean Tier 3 verifier rejected '{s}':\n{s}\n", .{ path, lean_res.stderr });
            try stderr.flush();
        } else {
            lean_summary = std.mem.trim(u8, lean_res.stdout, " \r\n\t");
        }
    }

    try stdout.print("Aethel Constitutional Verification: {s}\n", .{path});
    if (companion_path) |cp| {
        try stdout.print("  companion laws: {s}\n", .{cp});
    }
    for (checked.laws) |law| {
        switch (law.verdict) {
            .proved_tier0, .proved_tier1_exhaustive, .proved_tier2_symbolic, .proved_interval, .proved_tier3_lean => {
                const lean_note: []const u8 = if (lean_summary != null and (law.symbolic_certs.len > 0 or law.verdict == .proved_tier0))
                    " + Lean Tier 3"
                else
                    "";
                try stdout.print("  [PROVED]    {s} -- {s}{s}\n", .{ law.name, law.tier_detail, lean_note });
            },
            .falsified => {
                any_blocked = true;
                try stdout.print("  [FALSIFIED] {s} -- {s}\n", .{ law.name, law.counterexample orelse law.tier_detail });
            },
            .violated => {
                any_blocked = true;
                try stdout.print("  [VIOLATED]  {s} -- {s}\n", .{ law.name, law.tier_detail });
            },
            .unverified_symbolic => {
                any_blocked = true;
                try stdout.print("  [UNPROVED]  {s} -- requires Lean Tier 3 proof or bounded domain\n", .{law.name});
            },
        }
    }
    for (checked.functions) |cf| {
        if (cf.decreases_certs.len > 0) {
            const lean_note: []const u8 = if (lean_summary != null) " + Lean Tier 3" else "";
            try stdout.print("  [DECREASES] fn {s} -- {d} termination measure(s) proved{s}\n", .{
                cf.name,
                cf.decreases_certs.len,
                lean_note,
            });
        }
    }
    if (lean_summary) |ls| {
        try stdout.print("  [LEAN MIR]  {s}\n", .{ls});
    }
    if (checked.foreign_contracts.len > 0) {
        try stdout.print("  [FOREIGN]   Foreign contracts assumed: {d}\n", .{checked.foreign_contracts.len});
        for (checked.foreign_contracts) |fc| {
            if (fc.trait_name) |tn| {
                try stdout.print("              - instance {s}: {s} -> rust \"{s}\"\n", .{ fc.aethel_name, tn, fc.rust_sym });
            } else if (fc.rust_target) |rt| {
                try stdout.print("              - fn {s} -> rust crate \"{s}::{s}\"\n", .{ fc.aethel_name, rt, fc.rust_sym });
            } else {
                try stdout.print("              - fn {s} -> rust \"{s}\"\n", .{ fc.aethel_name, fc.rust_sym });
            }
        }
    }

    if (checked.hasErrors()) {
        for (checked.diagnostics) |diag| {
            try printLocatedCaretDiagnostic(stderr, loaded.slices, path, loaded.combined_source, diag.span, diag.message);
        }
        try stderr.flush();
    }

    if (any_blocked) {
        try stdout.print("Verdict: BLOCKED ({d} law(s), {d} decreases cert(s))\n", .{ checked.laws.len, total_decreases_certs });
        try stdout.flush();
        return 1;
    }

    try stdout.print("Verdict: ALL LAWS PROVED ({d} law(s), {d} decreases cert(s))\n", .{ checked.laws.len, total_decreases_certs });
    try stdout.flush();
    return 0;
}

fn slicesToModuleInfos(
    arena: std.mem.Allocator,
    slices: []const aethel.module_loader.SourceSlice,
) ![]const aethel.sema.ModuleSliceInfo {
    const out = try arena.alloc(aethel.sema.ModuleSliceInfo, slices.len);
    for (slices, 0..) |sl, i| {
        out[i] = .{
            .module_id = sl.module_id,
            .module_key = sl.module_key,
            .start = sl.start,
            .end = sl.end,
        };
    }
    return out;
}

fn printLoadedError(stderr: *Io.Writer, lerr: aethel.module_loader.LoadError) Io.Writer.Error!void {
    if (lerr.source.len == 0) {
        try stderr.print("{s}: error: {s}\n", .{ lerr.path, lerr.message });
    } else {
        try printCaretDiagnostic(stderr, lerr.path, lerr.source, lerr.span, lerr.message);
    }
}

fn printLocatedCaretDiagnostic(
    stderr: *Io.Writer,
    slices: []const aethel.module_loader.SourceSlice,
    fallback_path: []const u8,
    fallback_src: [:0]const u8,
    span: aethel.ast.Span,
    message: []const u8,
) Io.Writer.Error!void {
    if (aethel.module_loader.locateSpan(slices, span)) |loc| {
        try printCaretDiagnostic(stderr, loc.slice.path, loc.slice.source, loc.local_span, message);
    } else {
        try printCaretDiagnostic(stderr, fallback_path, fallback_src, span, message);
    }
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
        \\  aethel new <name> [--rust]
        \\  aethel add --rust <crate>[@<version>] [--features f1,f2] [--no-default-features] [--path <dir>]
        \\  aethel lex <file.aethel>
        \\  aethel parse <file.aethel>
        \\  aethel check [--explain-layout] [<file.aethel|dir>]
        \\  aethel verify [<file.aethel|dir>] [--laws <LAWS.aethel>] [--lean|--no-lean]
        \\  aethel emit-mir [<file.aethel|dir>]
        \\  aethel emit-zig [<file.aethel|dir>]
        \\  aethel emit-rust-adapter [<file.aethel|dir>]
        \\  aethel build [<file.aethel|dir>] [--rust <lib.rs|crate_dir>] [-o <out>] [-O debug|safe|fast|small] [--backend zig|llvm] [--release] [--offline] [--keep-zig]
        \\  aethel run [<file.aethel|dir>] [--rust <lib.rs|crate_dir>] [-O debug|safe|fast|small] [--backend zig|llvm] [--release] [--offline] [--keep-zig]
        \\
    , .{});
}

const CliTarget = struct {
    entry_path: []const u8,
    project_root: []const u8,
    manifest: ?aethel.manifest.ProjectManifest,
    pkg_name: ?[]const u8,
    declared_crates: ?[]const []const u8,
    user_rust_bridge: ?[]const u8,
};

fn resolveCliTarget(
    io: Io,
    arena: std.mem.Allocator,
    input_path: ?[]const u8,
    stderr: *Io.Writer,
) !?CliTarget {
    const is_dir_or_omitted = if (input_path) |ip|
        (aethel.manifest.isDirectory(io, ip) or std.mem.eql(u8, std.fs.path.basename(ip), "aethel.toml"))
    else
        true;

    const manifest_path_opt = try aethel.manifest.discoverManifestPath(io, arena, input_path);
    if (is_dir_or_omitted and manifest_path_opt == null) {
        try stderr.print("error: no aethel.toml found in target directory or ancestors (pass a .aethel file or run 'aethel new <name>')\n", .{});
        try stderr.flush();
        return null;
    }

    if (manifest_path_opt) |mp| {
        const toml_src = Io.Dir.cwd().readFileAllocOptions(io, mp, arena, .limited(2 * 1024 * 1024), .of(u8), 0) catch |err| {
            try stderr.print("error: failed to read manifest '{s}': {s}\n", .{ mp, @errorName(err) });
            try stderr.flush();
            return null;
        };
        const pm = aethel.manifest.parseManifest(arena, toml_src) catch |err| {
            try stderr.print("error: invalid aethel.toml '{s}' ({s})\n", .{ mp, @errorName(err) });
            try stderr.flush();
            return null;
        };
        const project_root = std.fs.path.dirname(mp) orelse ".";
        const entry_path = if (!is_dir_or_omitted and input_path != null)
            input_path.?
        else
            try aethel.manifest.resolveFromDir(arena, project_root, pm.entry);

        const declared = try arena.alloc([]const u8, pm.rust_deps.len);
        for (pm.rust_deps, 0..) |rd, di| declared[di] = rd.name;

        var bridge_path: ?[]const u8 = null;
        const bridge_cand = if (pm.rust_bridge) |rb|
            try aethel.manifest.resolveFromDir(arena, project_root, rb)
        else
            try aethel.manifest.resolveFromDir(arena, project_root, "rust/src/lib.rs");
        if (Io.Dir.cwd().access(io, bridge_cand, .{})) |_| {
            bridge_path = bridge_cand;
        } else |_| {
            if (pm.rust_bridge != null) {
                try stderr.print("error: configured [rust].bridge '{s}' not found\n", .{bridge_cand});
                try stderr.flush();
                return null;
            }
        }

        return .{
            .entry_path = entry_path,
            .project_root = project_root,
            .manifest = pm,
            .pkg_name = pm.pkg_name,
            .declared_crates = declared,
            .user_rust_bridge = bridge_path,
        };
    }

    return .{
        .entry_path = input_path.?,
        .project_root = ".",
        .manifest = null,
        .pkg_name = null,
        .declared_crates = null,
        .user_rust_bridge = null,
    };
}

fn runZigBuildExe(
    io: Io,
    arena: std.mem.Allocator,
    zig_path: []const u8,
    emit_bin_flag: []const u8,
    cache_dir: []const u8,
    opt_level: OptLevel,
    backend: BackendKind,
    strip_symbols: bool,
    rust_lib_opt: ?[]const u8,
    link_flags: []const []const u8,
    use_fno_lld: bool,
    use_flto: bool,
    stderr: *Io.Writer,
) !?std.process.RunResult {
    var argv_list: std.ArrayList([]const u8) = .empty;
    try argv_list.appendSlice(arena, &.{
        build_options.zig_exe,
        "build-exe",
        zig_path,
    });
    if (backend == .llvm) {
        try argv_list.append(arena, "-fllvm");
        if (use_flto) {
            try argv_list.append(arena, "-flto");
        }
        try argv_list.append(arena, if (strip_symbols) "-fstrip" else "-fno-strip");
    } else {
        try argv_list.append(arena, "-fno-llvm");
        if (use_fno_lld) {
            try argv_list.append(arena, "-fno-lld");
        }
    }
    if (rust_lib_opt) |rlib| {
        try argv_list.append(arena, rlib);
        for (link_flags) |lf| {
            try argv_list.append(arena, lf);
        }
    }
    switch (opt_level) {
        .debug => {},
        .safe => try argv_list.appendSlice(arena, &.{ "-O", "ReleaseSafe" }),
        .fast => try argv_list.appendSlice(arena, &.{ "-O", "ReleaseFast" }),
        .small => try argv_list.appendSlice(arena, &.{ "-O", "ReleaseSmall" }),
    }
    try argv_list.appendSlice(arena, &.{
        emit_bin_flag,
        "--cache-dir",
        cache_dir,
    });

    return std.process.run(arena, io, .{ .argv = argv_list.items }) catch |err| {
        try stderr.print("error: failed to invoke Zig compiler '{s}': {s}\n", .{ build_options.zig_exe, @errorName(err) });
        try stderr.flush();
        return null;
    };
}

fn handleNew(
    io: Io,
    arena: std.mem.Allocator,
    rest: []const []const u8,
    stdout: *Io.Writer,
    stderr: *Io.Writer,
) !u8 {
    var dir_opt: ?[]const u8 = null;
    var create_rust = false;
    for (rest) |arg| {
        if (std.mem.eql(u8, arg, "--rust")) {
            create_rust = true;
        } else if (std.mem.startsWith(u8, arg, "-")) {
            try stderr.print("error: unknown flag '{s}' for 'aethel new'\n", .{arg});
            try stderr.flush();
            return 2;
        } else if (dir_opt == null) {
            dir_opt = arg;
        } else {
            try stderr.print("usage: aethel new <name> [--rust]\n", .{});
            try stderr.flush();
            return 2;
        }
    }
    const dir = dir_opt orelse {
        try stderr.print("usage: aethel new <name> [--rust]\n", .{});
        try stderr.flush();
        return 2;
    };

    const pkg_name = try aethel.manifest.normalizePkgName(arena, dir);
    if (!aethel.manifest.isValidCrateIdent(pkg_name)) {
        try stderr.print("error: invalid package name '{s}' (must start with ASCII lowercase letter)\n", .{pkg_name});
        try stderr.flush();
        return 1;
    }

    const src_dir = try aethel.manifest.resolveFromDir(arena, dir, "src");
    try Io.Dir.cwd().createDirPath(io, src_dir);

    const toml_path = try aethel.manifest.resolveFromDir(arena, dir, "aethel.toml");
    if (Io.Dir.cwd().access(io, toml_path, .{})) |_| {
        try stderr.print("error: '{s}' already exists\n", .{toml_path});
        try stderr.flush();
        return 1;
    } else |_| {}

    const pm = aethel.manifest.ProjectManifest{ .pkg_name = pkg_name };
    const rendered_toml = try aethel.manifest.renderManifest(arena, &pm);
    try Io.Dir.cwd().writeFile(io, .{ .sub_path = toml_path, .data = rendered_toml });

    const gitignore_path = try aethel.manifest.resolveFromDir(arena, dir, ".gitignore");
    try Io.Dir.cwd().writeFile(io, .{ .sub_path = gitignore_path, .data = ".aethel-build/\nzig-out/\n" });

    const main_path = try aethel.manifest.resolveFromDir(arena, dir, "src/main.aethel");
    const main_src = try std.fmt.allocPrint(arena,
        \\pub fn main() {{
        \\  println("Hello from {s}!")
        \\}}
        \\
    , .{pkg_name});
    try Io.Dir.cwd().writeFile(io, .{ .sub_path = main_path, .data = main_src });

    if (create_rust) {
        const rust_dir = try aethel.manifest.resolveFromDir(arena, dir, "rust/src");
        try Io.Dir.cwd().createDirPath(io, rust_dir);
        const rust_lib = try aethel.manifest.resolveFromDir(arena, dir, "rust/src/lib.rs");
        try Io.Dir.cwd().writeFile(io, .{ .sub_path = rust_lib, .data = "// Optional Rust/Cargo bridge functions called via @external(rust, \"...\")\n" });
    }

    try stdout.print("Created Aethel project '{s}' at {s}\n", .{ pkg_name, dir });
    try stdout.flush();
    return 0;
}

fn handleAdd(
    io: Io,
    arena: std.mem.Allocator,
    rest: []const []const u8,
    stdout: *Io.Writer,
    stderr: *Io.Writer,
) !u8 {
    var is_rust = false;
    var spec_opt: ?[]const u8 = null;
    var path_opt: ?[]const u8 = null;
    var manifest_opt: ?[]const u8 = null;
    var default_features = true;
    var features_list: std.ArrayList([]const u8) = .empty;

    var i: usize = 0;
    while (i < rest.len) : (i += 1) {
        const arg = rest[i];
        if (std.mem.eql(u8, arg, "--rust")) {
            is_rust = true;
        } else if (std.mem.eql(u8, arg, "--no-default-features")) {
            default_features = false;
        } else if (std.mem.eql(u8, arg, "--features")) {
            i += 1;
            if (i >= rest.len) {
                try stderr.print("error: missing comma-separated features after '--features'\n", .{});
                try stderr.flush();
                return 2;
            }
            var it = std.mem.tokenizeAny(u8, rest[i], ", ");
            while (it.next()) |feat| try features_list.append(arena, feat);
        } else if (std.mem.eql(u8, arg, "--path")) {
            i += 1;
            if (i >= rest.len) {
                try stderr.print("error: missing crate path after '--path'\n", .{});
                try stderr.flush();
                return 2;
            }
            path_opt = rest[i];
        } else if (std.mem.eql(u8, arg, "--manifest-path")) {
            i += 1;
            if (i >= rest.len) {
                try stderr.print("error: missing path after '--manifest-path'\n", .{});
                try stderr.flush();
                return 2;
            }
            manifest_opt = rest[i];
        } else if (std.mem.startsWith(u8, arg, "-")) {
            try stderr.print("error: unknown flag '{s}' for 'aethel add'\n", .{arg});
            try stderr.flush();
            return 2;
        } else if (spec_opt == null) {
            spec_opt = arg;
        } else {
            try stderr.print("usage: aethel add --rust <crate>[@<version>] [--features f1,f2] [--no-default-features] [--path <dir>]\n", .{});
            try stderr.flush();
            return 2;
        }
    }

    const spec = spec_opt orelse {
        try stderr.print("usage: aethel add --rust <crate>[@<version>] [--features f1,f2] [--no-default-features] [--path <dir>]\n", .{});
        try stderr.flush();
        return 2;
    };

    if (!is_rust) {
        try stderr.print(
            \\error: native Aethel package registry ([dependencies]) is reserved for a future release;
            \\to add a Rust/Cargo crate to [rust-dependencies], run:
            \\  aethel add --rust {s}
            \\
        , .{spec});
        try stderr.flush();
        return 1;
    }

    const mp = manifest_opt orelse (try aethel.manifest.discoverManifestPath(io, arena, null)) orelse {
        try stderr.print("error: no aethel.toml found in current directory or ancestors (run 'aethel new <name>' first)\n", .{});
        try stderr.flush();
        return 1;
    };

    const toml_src = Io.Dir.cwd().readFileAllocOptions(io, mp, arena, .limited(2 * 1024 * 1024), .of(u8), 0) catch |err| {
        try stderr.print("error: failed to read '{s}': {s}\n", .{ mp, @errorName(err) });
        try stderr.flush();
        return 1;
    };
    const existing = aethel.manifest.parseManifest(arena, toml_src) catch |err| {
        try stderr.print("error: failed to parse '{s}': {s}\n", .{ mp, @errorName(err) });
        try stderr.flush();
        return 1;
    };

    const parsed = aethel.manifest.parseAddCrateSpec(spec);
    const ver_opt: ?[]const u8 = if (parsed.version != null)
        parsed.version
    else if (path_opt == null)
        "*"
    else
        null;

    const dep = aethel.manifest.RustDepSpec{
        .name = parsed.name,
        .version = ver_opt,
        .path = path_opt,
        .default_features = default_features,
        .features = try features_list.toOwnedSlice(arena),
    };
    const updated = aethel.manifest.upsertRustDependency(arena, &existing, dep) catch |err| {
        try stderr.print("error: invalid Rust dependency '{s}': {s}\n", .{ spec, @errorName(err) });
        try stderr.flush();
        return 1;
    };
    const rendered = try aethel.manifest.renderManifest(arena, &updated);
    try Io.Dir.cwd().writeFile(io, .{ .sub_path = mp, .data = rendered });

    try stdout.print("Added Rust crate '{s}' to [rust-dependencies] in {s}\n", .{ dep.name, mp });
    try stdout.flush();
    return 0;
}

test "main CLI module sanity check" {
    var tree = try aethel.parse(std.testing.allocator, "fn ok(x: u8) -> u8 { x }");
    defer tree.deinit();
    try std.testing.expect(!tree.hasErrors());
    var checked = try aethel.check(std.testing.allocator, &tree);
    defer checked.deinit();
    try std.testing.expect(!checked.hasErrors());
}
