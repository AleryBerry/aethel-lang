// Pure safe Rust ECS systems operating directly on Aethel's physical SoA split
// column queries and 64-byte aligned AoSoA(8) tile arrays!
// Zero unsafe blocks in user code: `aethel-zig/src/rust_ffi.zig` generates the
// C-ABI mirror structs and validated slice reconstruction shims automatically.

pub fn rust_integrate_positions(q: Entity_px_py_vx_vyQuery<'_>, step: PhysicsStep) {
    for i in 0..q.len {
        q.vx[i] *= step.damping;
        q.vy[i] *= step.damping;
        q.px[i] += q.vx[i] * step.dt;
        q.py[i] += q.vy[i] * step.dt;
    }
}

pub fn rust_apply_damage(q: Entity_healthQuery<'_>, dmg: i32) {
    for hp in q.health.iter_mut() {
        *hp = (*hp - dmg).max(0);
    }
}

pub fn rust_step_aosoa_tiles(a: SimdParticleAoSoAMut<'_>, dt: f32) {
    for tile in a.tiles.iter_mut() {
        for lane in 0..8 {
            tile.x[lane] += tile.vx[lane] * dt;
        }
    }
}
