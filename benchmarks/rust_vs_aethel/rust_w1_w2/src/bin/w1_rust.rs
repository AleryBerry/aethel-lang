use std::hint::black_box;
use std::mem::size_of;
use std::time::Instant;

#[allow(dead_code)]
struct Entity {
    f0: bool,
    f1: bool,
    f2: bool,
    f3: bool,
    f4: bool,
    f5: bool,
    f6: bool,
    f7: bool,
    team: u8,
    role: u8,
    hp: u16,
    x: f32,
    y: f32,
}

fn main() {
    let n: usize = 2_000_000;
    let passes: u32 = 25;
    let mut entities: Vec<Entity> = Vec::with_capacity(n);

    let t0 = Instant::now();
    let mut fx: f32 = 0.0;
    for i in 0..n {
        let idx = i as u32;
        let f0 = (idx & 1) == 0;
        let f1 = (idx & 2) != 0;
        let team = (idx & 15) as u8;
        let role = ((idx >> 4) & 15) as u8;
        let hp = ((idx & 255) as u16) + 100;
        entities.push(Entity {
            f0,
            f1,
            f2: false,
            f3: true,
            f4: false,
            f5: false,
            f6: true,
            f7: false,
            team,
            role,
            hp,
            x: fx,
            y: fx + 1.0,
        });
        fx += 0.25;
        if fx >= 1024.0 {
            fx = 0.0;
        }
    }

    let mut sum: u64 = 0;
    for p in 0..passes {
        for e in entities.iter_mut() {
            e.f0 = !e.f0;
            if e.f0 {
                e.hp = e.hp.wrapping_add(1);
                sum = sum.wrapping_add(e.hp as u64 + e.team as u64 + p as u64);
            } else {
                sum = sum.wrapping_add(e.role as u64);
            }
        }
    }

    let total = black_box(sum);
    let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let buf_bytes = entities.capacity() * size_of::<Entity>();
    println!(
        "w1_rust sizeof={} buf_bytes={} checksum={} ms={:.3}",
        size_of::<Entity>(),
        buf_bytes,
        total,
        elapsed_ms
    );
}
