use ::std::hint::black_box;
use ::std::time::Instant;

use ::bytemuck::{cast_slice, cast_slice_mut};
use ::rayon::prelude::*;
use ::regex::{Regex, RegexSet};
use ::tokio::sync::mpsc;

pub fn bench_serde(cfg: EngineConfig, iters: u32) -> u64 {
    let t0 = Instant::now();
    let mut acc: u64 = 0;
    for i in 0..iters {
        let mut cur = EngineConfig {
            fps: cfg.fps.wrapping_add(i & 31),
            vsync: cfg.vsync,
            worker_threads: cfg.worker_threads,
            bounds: cfg.bounds,
        };
        let s = ::serde_json::to_string(&cur).expect("serialize");
        let parsed: EngineConfig = ::serde_json::from_str(&s).expect("deserialize");
        cur = parsed;
        acc = acc.wrapping_add(cur.fps as u64 + cur.bounds.width as u64);
    }
    let ms = t0.elapsed().as_secs_f64() * 1000.0;
    eprintln!("stage serde_ms={:.3}", ms);
    black_box(acc)
}

pub fn bench_bytemuck(verts: &mut [GpuVertex]) -> u64 {
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
    let ms = t0.elapsed().as_secs_f64() * 1000.0;
    eprintln!("stage bytemuck_ms={:.3}", ms);
    black_box(sum)
}

pub fn bench_rayon(
    floats: &mut [f32],
    fma_chunk: impl Fn(&mut [f32]) + Sync,
    reduce_word: impl Fn(u32) -> u64 + Sync,
) -> u64 {
    let t0 = Instant::now();
    floats.par_chunks_mut(4096).for_each(|chunk| fma_chunk(chunk));
    let words: &[u32] = cast_slice(floats);
    let sum: u64 = words.par_iter().map(|&w| reduce_word(w)).sum();
    let ms = t0.elapsed().as_secs_f64() * 1000.0;
    eprintln!("stage rayon_ms={:.3}", ms);
    black_box(sum)
}

pub fn bench_tokio(msgs_per_producer: u32, on_msg: impl Fn(u32) -> u64) -> u64 {
    let t0 = Instant::now();
    let rt = ::tokio::runtime::Builder::new_multi_thread()
        .worker_threads(2)
        .enable_all()
        .build()
        .expect("tokio runtime");
    let total = rt.block_on(async move {
        let (tx, mut rx) = mpsc::channel::<u32>(64);
        let mut handles = Vec::with_capacity(4);
        for p in 0u32..4 {
            let ptx = tx.clone();
            handles.push(::tokio::spawn(async move {
                for k in 0..msgs_per_producer {
                    ptx.send(p * 1000 + k).await.expect("send");
                }
            }));
        }
        drop(tx);
        let mut acc: u64 = 0;
        while let Some(v) = rx.recv().await {
            acc = acc.wrapping_add(on_msg(v));
        }
        for h in handles {
            h.await.expect("join");
        }
        acc
    });
    let ms = t0.elapsed().as_secs_f64() * 1000.0;
    eprintln!("stage tokio_ms={:.3}", ms);
    black_box(total)
}

pub fn bench_regex(log_text: &str, on_cap: impl Fn(&str, u32) -> u64) -> u64 {
    let t0 = Instant::now();
    let set = RegexSet::new([r"ERROR", r"WARN", r"code=\d+"]).expect("regex set");
    let re = Regex::new(r"(?P<lvl>INFO|WARN|ERROR):(?P<mod>[a-z_]+)=(?P<code>\d+)").expect("regex");
    let set_hits = set.matches(log_text).into_iter().count() as u64;
    let mut acc = set_hits;
    for cap in re.captures_iter(log_text) {
        let lvl = cap.name("lvl").map(|m| m.as_str()).unwrap_or("");
        let code: u32 = cap["code"].parse().unwrap_or(0);
        acc = acc.wrapping_add(on_cap(lvl, code));
    }
    let ms = t0.elapsed().as_secs_f64() * 1000.0;
    eprintln!("stage regex_ms={:.3}", ms);
    black_box(acc)
}
