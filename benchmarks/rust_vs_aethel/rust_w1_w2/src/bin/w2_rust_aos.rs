use std::hint::black_box;
use std::mem::size_of;
use std::time::Instant;

#[allow(dead_code)]
struct Body32B {
    px: f32,
    py: f32,
    vx: f32,
    vy: f32,
    mass: f32,
    inv_mass: f32,
    flags: u32,
    id: u32,
}

fn main() {
    let n: usize = 1_000_000;
    let frames: u32 = 200;
    let dt: f32 = 0.016;
    let mut bodies: Vec<Body32B> = Vec::with_capacity(n);

    let t0 = Instant::now();
    let mut f: f32 = 0.0;
    for i in 0..n {
        let idx = i as u32;
        bodies.push(Body32B {
            px: f,
            py: f + 0.5,
            vx: 1.25,
            vy: -0.75,
            mass: 2.0,
            inv_mass: 0.5,
            flags: idx & 7,
            id: idx,
        });
        f += 0.125;
        if f >= 512.0 {
            f = 0.0;
        }
    }

    for _ in 0..frames {
        for b in bodies.iter_mut() {
            b.px += b.vx * dt;
            b.py += b.vy * dt;
        }
    }

    let mut acc: f32 = 0.0;
    for b in bodies.iter() {
        acc += (b.px + b.py) * 0.0001;
    }

    let total = black_box(acc);
    let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let buf_bytes = bodies.capacity() * size_of::<Body32B>();
    println!(
        "w2_rust_aos sizeof={} buf_bytes={} checksum={:.2} ms={:.3}",
        size_of::<Body32B>(),
        buf_bytes,
        total,
        elapsed_ms
    );
}
