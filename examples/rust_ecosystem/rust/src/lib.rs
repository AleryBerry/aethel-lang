use ::core::time::Duration;
use ::std::sync::Arc;
use ::bytemuck::{bytes_of, cast_slice, cast_slice_mut, from_bytes, try_cast_slice, Zeroable};
use ::rayon::prelude::*;
use ::regex::{Regex, RegexSet};
use ::tokio::sync::{mpsc, oneshot, RwLock, Semaphore};

/// 1. `serde` + `serde_json`: nested structs, field attributes (`rename`, `default`), DOM inspection, batch arrays, and invalid JSON errors.
pub fn test_serde_suite(
    cfg: EngineConfig,
    batch: &[TelemetryPoint],
    on_json: impl Fn(&str),
) -> bool {
    let json = ::serde_json::to_string(&cfg).expect("serialize nested EngineConfig");
    on_json(&json);

    let parsed: EngineConfig = ::serde_json::from_str(&json).expect("deserialize nested EngineConfig");
    if parsed != cfg || !json.contains("\"target_fps\"") {
        return false;
    }

    // Exercise #[serde(default)] when worker_threads is omitted.
    let partial = r#"{"target_fps":120,"vsync":false,"bounds":{"width":1920,"height":1080}}"#;
    let defaulted: EngineConfig = ::serde_json::from_str(partial).expect("serde default");
    if defaulted.fps != 120 || defaulted.vsync || defaulted.worker_threads != 0
        || defaulted.bounds.width != 1920 || defaulted.bounds.height != 1080
    {
        return false;
    }

    // Exercise batch slice serialization + serde_json::Value DOM + malformed JSON rejection.
    let batch_json = ::serde_json::to_string(batch).expect("serialize batch");
    let dom: ::serde_json::Value = ::serde_json::from_str(&batch_json).expect("parse DOM");
    let dom_len = dom.as_array().map(|a| a.len()).unwrap_or(0);
    let roundtrip: Vec<TelemetryPoint> = ::serde_json::from_value(dom).expect("from_value batch");
    let bad_err = ::serde_json::from_str::<EngineConfig>("{\"target_fps\":\"oops\"}").is_err();

    dom_len == batch.len() && roundtrip == batch && bad_err
}

/// 2. `bytemuck`: Zeroable, bytes_of/from_bytes, cast_slice, in-place cast_slice_mut, and try_cast_slice error checking.
pub fn test_bytemuck_suite(verts: &mut [GpuVertex]) -> u32 {
    let z = GpuVertex::zeroed();
    if z.x != 0.0 || z.y != 0.0 || z.z != 0.0 || z.rgba != 0 {
        return 0;
    }

    let first_bytes = bytes_of(&verts[0]);
    let decoded: &GpuVertex = from_bytes(first_bytes);
    if *decoded != verts[0] {
        return 0;
    }

    // Mutate alpha channel in-place via cast_slice_mut<GpuVertex, u32>.
    {
        let words: &mut [u32] = cast_slice_mut(verts);
        let mut idx = 3usize;
        while idx < words.len() {
            words[idx] = words[idx] | 0xFF00_0000;
            idx += 4;
        }
    }

    // Alignment error check: unaligned 1-byte offset slice must return Err.
    let raw_bytes = [0u8; 32];
    if try_cast_slice::<u8, GpuVertex>(&raw_bytes[1..17]).is_ok() {
        return 0;
    }

    let read_words: &[u32] = cast_slice(verts);
    let mut checksum: u32 = 0;
    for &w in read_words {
        checksum = checksum.wrapping_add(w);
    }
    checksum ^ (verts.len() as u32)
}

/// 3. `rayon`: par_chunks_mut (calling Aethel callback), par_iter().map().sum(), par_sort_unstable_by_key, and rayon::join.
pub fn test_rayon_suite(
    floats: &mut [f32],
    scores: &mut [ScoreEntry],
    fma_chunk: impl Fn(&mut [f32]) + Send + Sync,
    score_map: impl Fn(u32) -> u64 + Send + Sync,
) -> u64 {
    floats.par_chunks_mut(128).for_each(|chunk| {
        fma_chunk(chunk);
    });

    let mapped_sum: u64 = (0..16384u32)
        .into_par_iter()
        .map(|i| score_map(i))
        .sum();

    let (left_sum, right_sum) = ::rayon::join(
        || floats[..floats.len() / 2].iter().map(|&v| v as u64).sum::<u64>(),
        || floats[floats.len() / 2..].iter().map(|&v| v as u64).sum::<u64>(),
    );

    scores.par_sort_unstable_by_key(|s| s.score);

    mapped_sum.wrapping_add(left_sum).wrapping_add(right_sum)
}

/// 4. `tokio`: multi-thread runtime, mpsc producers, oneshot, Semaphore, RwLock, select!, and timeout cancellation.
pub fn test_tokio_suite(on_event: impl Fn(&str, u32) + Send + Sync + 'static + Copy) -> u32 {
    let rt = ::tokio::runtime::Builder::new_multi_thread()
        .worker_threads(2)
        .enable_all()
        .build()
        .expect("build tokio runtime");

    rt.block_on(async move {
        let (tx, mut rx) = mpsc::channel::<u32>(32);
        for p in 0..4u32 {
            let txc = tx.clone();
            ::tokio::spawn(async move {
                for j in 0..25u32 {
                    let _ = txc.send(p * 25 + j).await;
                }
            });
        }
        drop(tx);

        let mut mpsc_count = 0u32;
        while let Some(_v) = rx.recv().await {
            mpsc_count += 1;
        }
        on_event("mpsc_done", mpsc_count);

        // Semaphore + RwLock + oneshot
        let sem = Arc::new(Semaphore::new(2));
        let acc = Arc::new(RwLock::new(0u32));
        let mut handles = Vec::with_capacity(8);
        for tid in 1..=8u32 {
            let s = Arc::clone(&sem);
            let a = Arc::clone(&acc);
            handles.push(::tokio::spawn(async move {
                let _permit = s.acquire().await.unwrap();
                let mut g = a.write().await;
                *g += tid;
            }));
        }
        for h in handles {
            h.await.unwrap();
        }
        let rw_sum = *acc.read().await; // 1+..+8 = 36

        let (otx, orx) = oneshot::channel::<u32>();
        ::tokio::spawn(async move {
            ::tokio::time::sleep(Duration::from_millis(1)).await;
            let _ = otx.send(10);
        });

        let selected = ::tokio::select! {
            res = orx => res.unwrap_or(0),
            _ = ::tokio::time::sleep(Duration::from_secs(2)) => 0,
        };
        let timed_out = ::tokio::time::timeout(
            Duration::from_millis(2),
            ::tokio::time::sleep(Duration::from_secs(5)),
        )
        .await
        .is_err();

        on_event("tokio_sync", rw_sum + selected + if timed_out { 1 } else { 0 });
        mpsc_count + rw_sum + selected + if timed_out { 1 } else { 0 }
    })
}

/// 5. `regex`: named captures, RegexSet, replace_all redaction, and invalid pattern rejection.
pub fn test_regex_suite(
    log_text: &str,
    on_capture: impl Fn(&str, &str, u32),
) -> u32 {
    if Regex::new("[unclosed").is_ok() {
        return 0;
    }

    let cap_re = Regex::new(r"(?P<lvl>INFO|WARN|ERROR)\s+\[(?P<mod>[a-z_]+)\]\s+code=(?P<code>[0-9]+)")
        .expect("capture regex");
    let mut cap_count = 0u32;
    for c in cap_re.captures_iter(log_text) {
        let lvl = c.name("lvl").map(|m| m.as_str()).unwrap_or("");
        let mname = c.name("mod").map(|m| m.as_str()).unwrap_or("");
        let code: u32 = c.name("code").and_then(|m| m.as_str().parse().ok()).unwrap_or(0);
        on_capture(lvl, mname, code);
        cap_count += 1;
    }

    let set = RegexSet::new([r"ERROR", r"secret=[A-Za-z0-9_]+", r"code=200"]).expect("regex set");
    let mut set_hits = 0u32;
    for line in log_text.lines() {
        let m = set.matches(line);
        if m.matched_any() {
            set_hits += m.iter().count() as u32;
        }
    }

    let redact_re = Regex::new(r"secret=[A-Za-z0-9_]+").expect("redact regex");
    let redacted = redact_re.replace_all(log_text, "secret=[REDACTED]");
    if redacted.contains("hunter2") || !redacted.contains("secret=[REDACTED]") {
        return 0;
    }

    cap_count * 100 + set_hits
}
