use std::hint::black_box;
use std::time::Instant;

use bytemuck::{cast_slice, cast_slice_mut, Pod, Zeroable};
use rayon::prelude::*;
use regex::{Regex, RegexSet};
use serde::{Deserialize, Serialize};
use tokio::sync::mpsc;

#[derive(Clone, Copy, Serialize, Deserialize, PartialEq)]
struct WindowBounds {
    width: u32,
    height: u32,
}

#[derive(Clone, Copy, Serialize, Deserialize, PartialEq)]
struct EngineConfig {
    #[serde(rename = "target_fps")]
    fps: u32,
    vsync: bool,
    #[serde(default)]
    worker_threads: u32,
    bounds: WindowBounds,
}

#[repr(C)]
#[derive(Clone, Copy, Pod, Zeroable)]
struct GpuVertex {
    x: f32,
    y: f32,
    z: f32,
    rgba: u32,
}

#[inline(never)]
fn fma_chunk_rs(xs: &mut [f32]) {
    for x in xs.iter_mut() {
        *x = *x * 2.0 + 1.0;
    }
}

#[inline(never)]
fn reduce_word_rs(bits: u32) -> u64 {
    (bits as u64).wrapping_mul(3).wrapping_add(1)
}

#[inline(never)]
fn on_tokio_msg_rs(v: u32) -> u64 {
    (v as u64).wrapping_mul(3).wrapping_add(1)
}

#[inline(never)]
fn on_regex_cap_rs(lvl: &str, code: u32) -> u64 {
    (lvl.len() as u64) * 1000 + code as u64
}

fn bench_serde(cfg: EngineConfig, iters: u32) -> (u64, f64) {
    let t0 = Instant::now();
    let mut acc: u64 = 0;
    for i in 0..iters {
        let mut cur = cfg;
        cur.fps = cfg.fps.wrapping_add(i & 31);
        let s = serde_json::to_string(&cur).expect("serialize");
        let parsed: EngineConfig = serde_json::from_str(&s).expect("deserialize");
        acc = acc.wrapping_add(parsed.fps as u64 + parsed.bounds.width as u64);
    }
    (black_box(acc), t0.elapsed().as_secs_f64() * 1000.0)
}

fn bench_bytemuck(verts: &mut [GpuVertex]) -> (u64, f64) {
    let t0 = Instant::now();
    {
        let words: &mut [u32] = cast_slice_mut(verts);
        let mut idx = 3usize;
        while idx < words.len() {
            words[idx] |= 0xFF00_0000;
            idx += 4;
        }
    }
    let words: &[u32] = cast_slice(verts);
    let mut sum: u64 = 0;
    for &w in words {
        sum = sum.wrapping_add(w as u64);
    }
    (black_box(sum), t0.elapsed().as_secs_f64() * 1000.0)
}

fn bench_rayon(floats: &mut [f32]) -> (u64, f64) {
    let t0 = Instant::now();
    floats.par_chunks_mut(4096).for_each(fma_chunk_rs);
    let words: &[u32] = cast_slice(floats);
    let sum: u64 = words.par_iter().map(|&w| reduce_word_rs(w)).sum();
    (black_box(sum), t0.elapsed().as_secs_f64() * 1000.0)
}

fn bench_tokio(msgs_per_producer: u32) -> (u64, f64) {
    let t0 = Instant::now();
    let rt = tokio::runtime::Builder::new_multi_thread()
        .worker_threads(2)
        .enable_all()
        .build()
        .expect("tokio runtime");
    let total = rt.block_on(async move {
        let (tx, mut rx) = mpsc::channel::<u32>(64);
        let mut handles = Vec::with_capacity(4);
        for p in 0u32..4 {
            let ptx = tx.clone();
            handles.push(tokio::spawn(async move {
                for k in 0..msgs_per_producer {
                    ptx.send(p * 1000 + k).await.expect("send");
                }
            }));
        }
        drop(tx);
        let mut acc: u64 = 0;
        while let Some(v) = rx.recv().await {
            acc = acc.wrapping_add(on_tokio_msg_rs(v));
        }
        for h in handles {
            h.await.expect("join");
        }
        acc
    });
    (black_box(total), t0.elapsed().as_secs_f64() * 1000.0)
}

fn bench_regex(log_text: &str) -> (u64, f64) {
    let t0 = Instant::now();
    let set = RegexSet::new([r"ERROR", r"WARN", r"code=\d+"]).expect("regex set");
    let re = Regex::new(r"(?P<lvl>INFO|WARN|ERROR):(?P<mod>[a-z_]+)=(?P<code>\d+)").expect("regex");
    let set_hits = set.matches(log_text).into_iter().count() as u64;
    let mut acc = set_hits;
    for cap in re.captures_iter(log_text) {
        let lvl = cap.name("lvl").map(|m| m.as_str()).unwrap_or("");
        let code: u32 = cap["code"].parse().unwrap_or(0);
        acc = acc.wrapping_add(on_regex_cap_rs(lvl, code));
    }
    (black_box(acc), t0.elapsed().as_secs_f64() * 1000.0)
}

fn main() {
    let t_all = Instant::now();

    let cfg = EngineConfig {
        fps: 144,
        vsync: true,
        worker_threads: 4,
        bounds: WindowBounds {
            width: 2560,
            height: 1440,
        },
    };
    let (serde_sum, serde_ms) = bench_serde(cfg, 20_000);

    let mut verts = Vec::with_capacity(500_000);
    for i in 0u32..500_000 {
        verts.push(GpuVertex {
            x: 1.5,
            y: 2.5,
            z: 3.5,
            rgba: i & 0x00FF_FFFF,
        });
    }
    let (bytemuck_sum, bytemuck_ms) = bench_bytemuck(&mut verts);

    let mut floats = Vec::with_capacity(1_000_000);
    let mut fv: f32 = 0.0;
    for _ in 0..1_000_000 {
        floats.push(fv);
        fv += 0.25;
        if fv >= 128.0 {
            fv = 0.0;
        }
    }
    let (rayon_sum, rayon_ms) = bench_rayon(&mut floats);

    let (tokio_sum, tokio_ms) = bench_tokio(500);

    let unit = "INFO:render=200 WARN:audio=404 ERROR:ecs=500 INFO:io=101\n";
    let mut log_text = String::with_capacity(unit.len() * 2500);
    for _ in 0..2500 {
        log_text.push_str(unit);
    }
    let (regex_sum, regex_ms) = bench_regex(&log_text);

    let total_sum = serde_sum
        .wrapping_add(bytemuck_sum)
        .wrapping_add(rayon_sum)
        .wrapping_add(tokio_sum)
        .wrapping_add(regex_sum);
    let total_ms = t_all.elapsed().as_secs_f64() * 1000.0;

    println!(
        "w3_rust_eco serde_ms={:.3} bytemuck_ms={:.3} rayon_ms={:.3} tokio_ms={:.3} regex_ms={:.3} total_ms={:.3} checksum={}",
        serde_ms, bytemuck_ms, rayon_ms, tokio_ms, regex_ms, total_ms, total_sum
    );
}
