// Pure safe Rust slices (auto-wrapped via C-ABI shims by `aethel-zig/src/rust_ffi.zig`)
// paired with explicit `extern "C"` opaque RustOwn heap-handle functions.
use core::ffi::c_void;

pub fn fast_dot(xs: &[f32], ys: &[f32]) -> f32 {
    let n = if xs.len() < ys.len() { xs.len() } else { ys.len() };
    let mut acc = 0.0f32;
    let mut i = 0usize;
    while i < n {
        acc += xs[i] * ys[i];
        i += 1;
    }
    acc
}

pub fn scale_in_place(xs: &mut [f32], factor: f32) {
    for x in xs.iter_mut() {
        *x *= factor;
    }
}

#[no_mangle]
pub unsafe extern "C" fn rust_buf_new() -> *mut c_void {
    let b = Box::new(Vec::<i32>::new());
    Box::into_raw(b) as *mut c_void
}

#[no_mangle]
pub unsafe extern "C" fn rust_buf_push(ptr: *mut c_void, val: i32) {
    let vec = &mut *(ptr as *mut Vec<i32>);
    vec.push(val);
}

#[no_mangle]
pub unsafe extern "C" fn rust_buf_sum(ptr: *const c_void) -> i32 {
    let vec = &*(ptr as *const Vec<i32>);
    vec.iter().copied().sum()
}

#[no_mangle]
pub unsafe extern "C" fn rust_buf_drop(ptr: *mut c_void) {
    let _ = Box::from_raw(ptr as *mut Vec<i32>);
}
