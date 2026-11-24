const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const build_options = b.addOptions();
    build_options.addOption([]const u8, "zig_exe", b.graph.zig_exe);
    build_options.addOption([]const u8, "lean_dir", b.pathResolve(&.{ b.root.root_dir.path orelse ".", b.root.sub_path, "../aethel-lean" }));
    build_options.addOption([]const u8, "std_dir", b.pathResolve(&.{ b.root.root_dir.path orelse ".", b.root.sub_path, "../std" }));

    const build_options_mod = build_options.createModule();

    const mod = b.addModule("aethel", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
    });
    mod.addImport("build_options", build_options_mod);

    const exe = b.addExecutable(.{
        .name = "aethel",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "aethel", .module = mod },
            },
        }),
    });
    exe.root_module.addImport("build_options", build_options_mod);

    b.installArtifact(exe);

    const run_step = b.step("run", "Run the Aethel frontend CLI");
    const run_cmd = b.addRunArtifact(exe);
    run_step.dependOn(&run_cmd.step);
    run_cmd.step.dependOn(b.getInstallStep());
    run_cmd.addPassthruArgs();

    const mod_tests = b.addTest(.{
        .root_module = mod,
    });
    const run_mod_tests = b.addRunArtifact(mod_tests);

    const exe_tests = b.addTest(.{
        .root_module = exe.root_module,
    });
    const run_exe_tests = b.addRunArtifact(exe_tests);

    const test_step = b.step("test", "Run Aethel Zig unit and fuzz tests");
    test_step.dependOn(&run_mod_tests.step);
    test_step.dependOn(&run_exe_tests.step);
}
