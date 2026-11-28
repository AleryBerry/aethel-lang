pub fn rust_step_soa(q: Body32B_px_py_vx_vyQuery, dt: f32) {
    let n = q.len;
    let px = &mut q.px[..n];
    let py = &mut q.py[..n];
    let vx = &q.vx[..n];
    let vy = &q.vy[..n];
    for (((x, y), &dx), &dy) in px.iter_mut().zip(py.iter_mut()).zip(vx.iter()).zip(vy.iter()) {
        *x += dx * dt;
        *y += dy * dt;
    }
}
