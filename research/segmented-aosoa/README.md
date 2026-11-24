# Segmented AoSoA growth experiment

A tile owns contiguous columns of a fixed width. The directory can move while its tiles stay in their original allocations. An append fills one lane or allocates a tile at capacity. The Lean model proves these operations for one byte per field and tracks provenance with the byte machine. A valid active view retains its byte and permissions. Tile allocation takes place only at a boundary and uses a fresh owner identity. [Lean model](../../aethel-lean/Aethel/SegmentedAoSoA.lean)

The contiguous comparison uses the same tile layout with geometric buffer growth. Both implementations use `std.heap.smp_allocator`, a 64-byte-aligned tile base, four one-byte fields, and identical input rows. Tile widths are 16, 64, and 256. Row counts straddle two doubling boundaries and include partial tails. Every sample checks a hot-field and full-row checksum against logical rows. The segmented sample also checks the first tile's address after growth.

```sh
zig build-exe -O ReleaseFast -fno-llvm -fno-lld \
  research/segmented-aosoa/bench.zig -femit-bin=/tmp/aethel-segmented-aosoa-bench
taskset -c 2 /tmp/aethel-segmented-aosoa-bench
```

Select Zig 0.17.0 through zvm. For CPU affinity, use a core available to the current process. The program prints all comparisons as CSV. This run used CPU 2 on an Intel Core i5-7400 with a 32 KiB L1 data cache and 64-byte lines. The four-field payloads occupy about 16 KiB and 512 KiB. Segmented directories also occupy cache space. Hardware L1 miss counts were unavailable on this host.

## Observed results

The table reports medians of nine samples for 64-lane tiles. The benchmark warms both representations, alternates their order, and reports scan time per pass. Peak and directory values count allocator-requested bytes, excluding allocator overhead. Payload copies count relocation on growth. Directory bytes show the final directory allocation and directory copies count pointer relocation.

| Rows | Storage | Append µs | Hot scan µs | Full scan µs | Allocations | Peak B | Payload copied B | Directory B | Directory copied B |
|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 4,093 | contiguous | 174.6 | 9.75 | 25.83 | 7 | 24,576 | 16,128 | 0 | 0 |
| 4,093 | segmented | 147.2 | 9.76 | 26.15 | 71 | 16,896 | 0 | 512 | 504 |
| 4,099 | contiguous | 200.9 | 9.96 | 25.94 | 8 | 49,152 | 32,512 | 0 | 0 |
| 4,099 | segmented | 159.2 | 9.97 | 25.22 | 73 | 17,920 | 0 | 1,024 | 1,016 |
| 131,069 | contiguous | 6840.0 | 315.80 | 839.95 | 12 | 786,432 | 524,032 | 0 | 0 |
| 131,069 | segmented | 4672.9 | 360.52 | 855.04 | 2,060 | 540,672 | 0 | 16,384 | 16,376 |
| 131,075 | contiguous | 7087.9 | 362.76 | 863.01 | 13 | 1,572,864 | 1,048,320 | 0 | 0 |
| 131,075 | segmented | 4949.3 | 354.96 | 872.01 | 2,062 | 573,440 | 0 | 32,768 | 32,760 |

For 131,075 rows and 64-lane tiles, segmented growth eliminated 1,048,320 bytes of payload copying and used 573,440 peak requested bytes, down from 1,572,864. It made 2,062 allocation requests, up from 13. Immediately before that doubling boundary, its hot-field scan took about 14% longer. At 16 lanes and 131,075 rows, the hot-field scan took about 29% longer. The 256-lane comparison at the same size was roughly even on scans. These timings describe this microbenchmark and allocator. Compiler layout selection needs workload measurements and a verified lowering from Aethel operations.

