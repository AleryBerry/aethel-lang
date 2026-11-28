#!/usr/bin/env python3
"""
Rust vs. Aethel Fair Benchmark Runner (Release Mode + Isolated Peak RSS)

Workloads:
  W1: Dense Bit-Packed Layout (2,000,000 entities x 25 passes)
      w1_rust (20B #[repr(Rust)]) vs w1_aethel (12B FFD bit-packed)
  W2: Hot-Field Streaming SoA vs AoS (1,000,000 32B bodies x 200 frames)
      w2_rust_aos vs w2_aethel_soa vs w2_aethel_hybrid
  W3: 5-Crate Rust Ecosystem Integration (serde+serde_json, bytemuck, rayon, tokio, regex)
      w3_rust_eco vs w3_aethel_eco
"""

import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
AETHEL = Path("/home/aleryberry/Projects/aethel-lang/aethel-zig/zig-out/bin/aethel")
ITERATIONS = 5


def run_cmd(cmd, cwd, env=None):
    print(f"+ ({cwd.name}) {' '.join(str(c) for c in cmd)}")
    res = subprocess.run(cmd, cwd=cwd, env=env, text=True)
    if res.returncode != 0:
        raise RuntimeError(f"Command failed ({res.returncode}): {' '.join(map(str, cmd))}")


def exec_isolated(bin_path: Path):
    """Run bin_path in a clean child process and measure wall-clock ms and ru_maxrss (KiB)."""
    with tempfile.TemporaryFile(mode="w+b") as out_f, tempfile.TemporaryFile(mode="w+b") as err_f:
        out_fd = out_f.fileno()
        err_fd = err_f.fileno()
        t0 = time.perf_counter()
        pid = os.fork()
        if pid == 0:
            os.dup2(out_fd, 1)
            os.dup2(err_fd, 2)
            os.execv(str(bin_path), [str(bin_path)])
            os._exit(127)
        _, status, rusage = os.wait4(pid, 0)
        t1 = time.perf_counter()
        out_f.seek(0)
        err_f.seek(0)
        output = (
            out_f.read().decode("utf-8", errors="replace")
            + "\n"
            + err_f.read().decode("utf-8", errors="replace")
        )
        if not os.WIFEXITED(status) or os.WEXITSTATUS(status) != 0:
            raise RuntimeError(f"{bin_path.name} failed (status={status}):\n{output}")
    return {
        "wall_ms": (t1 - t0) * 1000.0,
        "max_rss_kib": float(rusage.ru_maxrss),
        "output": output,
    }


def parse_metrics(output: str):
    metrics = {}
    for m in re.finditer(r"([a-zA-Z_][a-zA-Z0-9_]*)=([^\s]+)", output):
        k, v = m.group(1), m.group(2)
        try:
            if "." in v:
                metrics[k] = float(v)
            else:
                metrics[k] = int(v)
        except ValueError:
            metrics[k] = v
    return metrics


def build_all(bin_dir: Path):
    bin_dir.mkdir(parents=True, exist_ok=True)

    # Ensure Cargo.lock exists for W3 projects so --offline succeeds cleanly.
    lock_src = ROOT.parent.parent / "examples" / "rust_ecosystem" / "Cargo.lock"
    for target_lock in [ROOT / "rust_w3_eco" / "Cargo.lock", ROOT / "aethel_w3_eco" / "Cargo.lock"]:
        if not target_lock.exists() and lock_src.exists():
            shutil.copy2(lock_src, target_lock)

    native_rust_env = {**os.environ, "RUSTFLAGS": "-C target-cpu=native"}
    run_cmd(["cargo", "build", "--release", "--offline"], ROOT / "rust_w1_w2", env=native_rust_env)
    run_cmd(["cargo", "build", "--release", "--offline"], ROOT / "rust_w3_eco", env=native_rust_env)

    targets = [
        ("aethel_w1", bin_dir / "w1_aethel", False, "llvm"),
        ("aethel_w1", bin_dir / "w1_aethel_zigbe", False, "zig"),
        ("aethel_w2_soa", bin_dir / "w2_aethel_soa", False, "llvm"),
        ("aethel_w2_soa", bin_dir / "w2_aethel_soa_zigbe", False, "zig"),
        ("aethel_w2_hybrid", bin_dir / "w2_aethel_hybrid", False, "llvm"),
        ("aethel_w3_eco", bin_dir / "w3_aethel_eco", True, "llvm"),
    ]
    for folder, out_bin, offline, backend in targets:
        cmd = [str(AETHEL), "build", "-O", "fast", "--release", "--backend", backend, "-o", str(out_bin)]
        if offline:
            cmd.append("--offline")
        run_cmd(cmd, ROOT / folder)

    bins = {
        "w1_rust": ROOT / "rust_w1_w2" / "target" / "release" / "w1_rust",
        "w1_aethel": bin_dir / "w1_aethel",
        "w1_aethel_zigbe": bin_dir / "w1_aethel_zigbe",
        "w2_rust_aos": ROOT / "rust_w1_w2" / "target" / "release" / "w2_rust_aos",
        "w2_aethel_soa": bin_dir / "w2_aethel_soa",
        "w2_aethel_soa_zigbe": bin_dir / "w2_aethel_soa_zigbe",
        "w2_aethel_hybrid": bin_dir / "w2_aethel_hybrid",
        "w3_rust_eco": ROOT / "rust_w3_eco" / "target" / "release" / "rust_w3_eco",
        "w3_aethel_eco": bin_dir / "w3_aethel_eco",
    }
    return bins


def measure_target(name: str, bin_path: Path, iterations: int = ITERATIONS):
    # 1 warmup
    warm = exec_isolated(bin_path)
    runs = [exec_isolated(bin_path) for _ in range(iterations)]
    walls = [r["wall_ms"] for r in runs]
    rss_kibs = [r["max_rss_kib"] for r in runs]
    parsed_runs = [parse_metrics(r["output"]) for r in runs]
    last_metrics = parsed_runs[-1]

    stage_medians = {}
    for k in ("ms", "serde_ms", "bytemuck_ms", "rayon_ms", "tokio_ms", "regex_ms", "total_ms"):
        vals = [m[k] for m in parsed_runs if k in m]
        if len(vals) == len(parsed_runs):
            stage_medians[k] = statistics.median(vals)

    return {
        "name": name,
        "bin_kib": bin_path.stat().st_size / 1024.0,
        "wall_med_ms": statistics.median(walls),
        "wall_min_ms": min(walls),
        "wall_max_ms": max(walls),
        "rss_med_kib": statistics.median(rss_kibs),
        "rss_min_kib": min(rss_kibs),
        "rss_max_kib": max(rss_kibs),
        "metrics": last_metrics,
        "stage_medians": stage_medians,
        "sample_output": warm["output"].strip(),
    }


def main():
    bin_dir = ROOT / ".bench-bin"
    bins = build_all(bin_dir)

    print("\n=== Running Benchmarks (1 warmup + 5 measured runs each) ===")
    results = {}
    for name, path in bins.items():
        r = measure_target(name, path)
        results[name] = r
        print(
            f"[{name}] bin={r['bin_kib']:.1f} KiB | "
            f"wall={r['wall_med_ms']:.2f} ms (min={r['wall_min_ms']:.2f}, max={r['wall_max_ms']:.2f}) | "
            f"rss={r['rss_med_kib']:.0f} KiB ({r['rss_med_kib']/1024.0:.2f} MiB) | "
            f"checksum={r['metrics'].get('checksum')}"
        )

    # Checksum parity verification
    c_w1_r = results["w1_rust"]["metrics"].get("checksum")
    c_w1_a = results["w1_aethel"]["metrics"].get("checksum")
    c_w1_z = results["w1_aethel_zigbe"]["metrics"].get("checksum")
    if c_w1_r != c_w1_a or c_w1_r != c_w1_z:
        print(f"ERROR: W1 checksum mismatch: rust={c_w1_r} vs llvm={c_w1_a} vs zig={c_w1_z}", file=sys.stderr)
        sys.exit(1)

    c_w2_r = float(results["w2_rust_aos"]["metrics"].get("checksum"))
    c_w2_s = float(results["w2_aethel_soa"]["metrics"].get("checksum"))
    c_w2_z = float(results["w2_aethel_soa_zigbe"]["metrics"].get("checksum"))
    c_w2_h = float(results["w2_aethel_hybrid"]["metrics"].get("checksum"))
    if abs(c_w2_r - c_w2_s) > 0.5 or abs(c_w2_r - c_w2_z) > 0.5 or abs(c_w2_r - c_w2_h) > 0.5:
        print(f"ERROR: W2 checksum mismatch: rust={c_w2_r}, soa_llvm={c_w2_s}, soa_zig={c_w2_z}, hybrid={c_w2_h}", file=sys.stderr)
        sys.exit(1)

    c_w3_r = results["w3_rust_eco"]["metrics"].get("checksum")
    c_w3_a = results["w3_aethel_eco"]["metrics"].get("checksum")
    if c_w3_r != c_w3_a:
        print(f"ERROR: W3 checksum mismatch: rust={c_w3_r} vs aethel={c_w3_a}", file=sys.stderr)
        sys.exit(1)

    print("\n=== Checksum Parity Verified ===")
    print(f"W1: {c_w1_r} == {c_w1_a} == {c_w1_z}")
    print(f"W2: {c_w2_r:.2f} ~= {c_w2_s:.3f} ~= {c_w2_z:.3f} ~= {c_w2_h:.3f}")
    print(f"W3: {c_w3_r} == {c_w3_a}")

    print("\n=== W3 Per-Stage Median Breakdown (ms) ===")
    for stage in ("serde_ms", "bytemuck_ms", "rayon_ms", "tokio_ms", "regex_ms"):
        r_ms = results["w3_rust_eco"]["stage_medians"].get(stage, float("nan"))
        a_ms = results["w3_aethel_eco"]["stage_medians"].get(stage, float("nan"))
        ratio = a_ms / r_ms if r_ms else float("nan")
        print(f"  {stage:12s}: Rust={r_ms:8.3f} ms | Aethel={a_ms:8.3f} ms | Aethel/Rust={ratio:.2f}x")


if __name__ == "__main__":
    main()
