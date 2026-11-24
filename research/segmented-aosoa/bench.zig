const std = @import("std");

const field_count = 4;
const sample_count = 9;
const allocator = std.heap.smp_allocator;
const cache_alignment: std.mem.Alignment = .fromByteUnits(64);

const StorageStats = struct {
    allocations: usize = 0,
    live: usize = 0,
    peak: usize = 0,
    payload_copied: usize = 0,
    directory_copied: usize = 0,

    fn alloc(self: *StorageStats, bytes: usize) void {
        self.allocations += 1;
        self.live += bytes;
        self.peak = @max(self.peak, self.live);
    }
};

fn Vector(comptime width: usize, comptime segmented: bool) type {
    const Tile = [field_count][width]u8;
    const TilePtr = *align(64) Tile;
    return struct {
        const Self = @This();
        contiguous: []align(64) Tile = &.{},
        directory: []TilePtr = &.{},
        length: usize = 0,
        stats: StorageStats = .{},

        fn deinit(self: Self) void {
            if (segmented) {
                const used = std.math.divCeil(usize, self.length, width) catch unreachable;
                for (self.directory[0..used]) |ptr| {
                    allocator.free(@as([*]align(64) Tile, @ptrCast(ptr))[0..1]);
                }
                allocator.free(self.directory);
            } else allocator.free(self.contiguous);
        }

        fn addTile(self: *Self, index: usize) !void {
            if (segmented) {
                if (index == self.directory.len) {
                    const new_dir = try allocator.alloc(TilePtr, @max(1, self.directory.len * 2));
                    self.stats.alloc(new_dir.len * @sizeOf(TilePtr));
                    @memcpy(new_dir[0..index], self.directory);
                    const old_bytes = self.directory.len * @sizeOf(TilePtr);
                    self.stats.directory_copied += old_bytes;
                    allocator.free(self.directory);
                    self.stats.live -= old_bytes;
                    self.directory = new_dir;
                }
                const allocation = try allocator.alignedAlloc(Tile, cache_alignment, 1);
                self.stats.alloc(@sizeOf(Tile));
                self.directory[index] = &allocation[0];
            } else if (index == self.contiguous.len) {
                const new_tiles = try allocator.alignedAlloc(Tile, cache_alignment, @max(1, index * 2));
                self.stats.alloc(new_tiles.len * @sizeOf(Tile));
                @memcpy(new_tiles[0..index], self.contiguous);
                const old_bytes = self.contiguous.len * @sizeOf(Tile);
                self.stats.payload_copied += old_bytes;
                allocator.free(self.contiguous);
                self.stats.live -= old_bytes;
                self.contiguous = new_tiles;
            }
        }

        fn tile(self: Self, index: usize) TilePtr {
            if (segmented) return self.directory[index];
            // Each Tile is a multiple of 64 bytes, and the array base is aligned.
            return @alignCast(&self.contiguous[index]);
        }

        fn append(self: *Self, row: [field_count]u8) !void {
            const index = self.length / width;
            const lane = self.length % width;
            if (lane == 0) try self.addTile(index);
            const ptr = self.tile(index);
            inline for (0..field_count) |field| ptr[field][lane] = row[field];
            self.length += 1;
        }

        noinline fn scan(self: *const Self, comptime hot_only: bool) u64 {
            var sum: u64 = 0;
            var start: usize = 0;
            while (start < self.length) : (start += width) {
                const ptr = self.tile(start / width);
                const lanes = @min(width, self.length - start);
                for (0..lanes) |lane| {
                    if (hot_only) {
                        sum += ptr[0][lane];
                    } else {
                        inline for (0..field_count) |field| sum += ptr[field][lane];
                    }
                }
            }
            return sum;
        }
    };
}

fn makeRow(index: usize, seed: u8) [field_count]u8 {
    const value: u8 = @truncate(index *% 17 +% seed);
    return .{ value, value ^ 87, value +% 11, value *% 5 };
}

const Sample = struct {
    append_ns: i96,
    hot_ns: i96,
    full_ns: i96,
    stats: StorageStats,
    directory_bytes: usize,
};

fn sample(comptime width: usize, comptime segmented: bool, io: std.Io, rows: usize, seed: u8) !Sample {
    var vector: Vector(width, segmented) = .{};
    defer vector.deinit();
    const start = std.Io.Clock.awake.now(io);
    try vector.append(makeRow(0, seed));
    const first_tile = vector.tile(0);
    for (1..rows) |index| try vector.append(makeRow(index, seed));
    const appended = std.Io.Clock.awake.now(io);

    var expected_hot: u64 = 0;
    var expected_full: u64 = 0;
    for (0..rows) |index| {
        const row = makeRow(index, seed);
        expected_hot += row[0];
        for (row) |byte| expected_full += byte;
    }
    if (segmented and vector.tile(0) != first_tile) return error.MovedTile;
    if (vector.scan(true) != expected_hot or vector.scan(false) != expected_full)
        return error.ChecksumMismatch;

    const repeats = @max(16, 1_048_576 / rows);
    const hot_start = std.Io.Clock.awake.now(io);
    for (0..repeats) |_| {
        std.mem.doNotOptimizeAway(&vector);
        std.mem.doNotOptimizeAway(vector.scan(true));
    }
    const full_start = std.Io.Clock.awake.now(io);
    for (0..repeats) |_| {
        std.mem.doNotOptimizeAway(&vector);
        std.mem.doNotOptimizeAway(vector.scan(false));
    }
    const end = std.Io.Clock.awake.now(io);
    return .{
        .append_ns = start.durationTo(appended).nanoseconds,
        .hot_ns = @divTrunc(hot_start.durationTo(full_start).nanoseconds, @as(i96, @intCast(repeats))),
        .full_ns = @divTrunc(full_start.durationTo(end).nanoseconds, @as(i96, @intCast(repeats))),
        .stats = vector.stats,
        .directory_bytes = vector.directory.len * @sizeOf(*anyopaque),
    };
}

fn median(samples: [sample_count]Sample, comptime field: []const u8) i96 {
    var timings: [sample_count]i96 = undefined;
    for (samples, &timings) |measurement, *timing| timing.* = @field(measurement, field);
    std.mem.sort(i96, &timings, {}, comptime std.sort.asc(i96));
    return timings[sample_count / 2];
}

fn report(out: *std.Io.Writer, rows: usize, width: usize, name: []const u8, samples: [sample_count]Sample) !void {
    const first = samples[0];
    try out.print("{d},{d},{s},{d},{d},{d},{d},{d},{d},{d},{d}\n", .{
        rows,                         width,                   name,             median(samples, "append_ns"), median(samples, "hot_ns"),
        median(samples, "full_ns"),   first.stats.allocations, first.stats.peak, first.stats.payload_copied,   first.directory_bytes,
        first.stats.directory_copied,
    });
}

pub fn main(init: std.process.Init) !void {
    var buffer: [4096]u8 = undefined;
    var stdout = std.Io.File.stdout().writer(init.io, &buffer);
    const out = &stdout.interface;
    try out.writeAll("rows,width,storage,append_ns,hot_scan_ns,full_scan_ns,allocations,peak_requested_bytes,payload_copied_bytes,directory_bytes,directory_copied_bytes\n");
    inline for (.{ 16, 64, 256 }) |width| {
        for ([_]usize{ 4_093, 4_099, 131_069, 131_075 }) |rows| {
            _ = try sample(width, false, init.io, rows, 0);
            _ = try sample(width, true, init.io, rows, 0);
            var contiguous: [sample_count]Sample = undefined;
            var segmented: [sample_count]Sample = undefined;
            for (0..sample_count) |i| {
                const seed: u8 = @intCast(i + 1);
                if (i % 2 == 0) {
                    contiguous[i] = try sample(width, false, init.io, rows, seed);
                    segmented[i] = try sample(width, true, init.io, rows, seed);
                } else {
                    segmented[i] = try sample(width, true, init.io, rows, seed);
                    contiguous[i] = try sample(width, false, init.io, rows, seed);
                }
            }
            try report(out, rows, width, "contiguous", contiguous);
            try report(out, rows, width, "segmented", segmented);
        }
    }
    try out.flush();
}
