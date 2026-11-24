const std = @import("std");

pub const StdModule = struct {
    key: []const u8,
    source: [:0]const u8,
};

pub const modules = [_]StdModule{
    .{
        .key = "std/cmp",
        .source =
        \\//// Ordering, Equality, and Hashing traits for Aethel containers and algorithms.
        \\
        \\pub type Ordering {
        \\  Lt
        \\  Eq
        \\  Gt
        \\}
        \\
        \\pub trait Eq(a) {
        \\  fn eq(x: a, y: a) -> bool
        \\  law refl(x: a) {
        \\    always eq(x, x) == true
        \\  }
        \\  law sym(x: a, y: a) {
        \\    always eq(x, y) == eq(y, x)
        \\  }
        \\}
        \\
        \\pub trait Ord(a) <= Eq(a) {
        \\  fn compare(x: a, y: a) -> Ordering
        \\}
        \\
        \\pub trait Hash(a) <= Eq(a) {
        \\  fn hash(x: a) -> u64
        \\}
        \\
        \\pub default instance eq_u32: Eq(u32) {
        \\  fn eq(x: u32, y: u32) -> bool { x == y }
        \\}
        \\
        \\pub default instance eq_u8: Eq(u8) {
        \\  fn eq(x: u8, y: u8) -> bool { x == y }
        \\}
        \\
        \\pub default instance eq_i8: Eq(i8) {
        \\  fn eq(x: i8, y: i8) -> bool { x == y }
        \\}
        \\
        \\pub default instance eq_bool: Eq(bool) {
        \\  fn eq(x: bool, y: bool) -> bool { (x && y) || (!x && !y) }
        \\}
        \\
        \\pub fn is_lt(o: Ordering) -> bool {
        \\  case o {
        \\    Lt -> true
        \\    Eq -> false
        \\    Gt -> false
        \\  }
        \\}
        \\
        \\pub fn is_eq(o: Ordering) -> bool {
        \\  case o {
        \\    Eq -> true
        \\    Lt -> false
        \\    Gt -> false
        \\  }
        \\}
        \\
        \\pub fn is_gt(o: Ordering) -> bool {
        \\  case o {
        \\    Gt -> true
        \\    Lt -> false
        \\    Eq -> false
        \\  }
        \\}
        \\
        \\pub fn reverse_ord(o: Ordering) -> Ordering {
        \\  case o {
        \\    Lt -> Gt
        \\    Eq -> Eq
        \\    Gt -> Lt
        \\  }
        \\}
        \\
        \\pub fn compare_u32(a: u32, b: u32) -> Ordering {
        \\  if a < b {
        \\    Lt
        \\  } else if a > b {
        \\    Gt
        \\  } else {
        \\    Eq
        \\  }
        \\}
        \\
        \\pub fn compare_i32(a: i32, b: i32) -> Ordering {
        \\  if a < b {
        \\    Lt
        \\  } else if a > b {
        \\    Gt
        \\  } else {
        \\    Eq
        \\  }
        \\}
        \\
        ,
    },
    .{
        .key = "std/traits",
        .source =
        \\//// Core categorical trait hierarchy for Aethel (`Semigroup <= Monoid`,
        \\//// `Functor <= Applicative <= Monad`), verified by Constitutional Laws.
        \\
        \\pub trait Semigroup(a) {
        \\  fn combine(x: a, y: a) -> a
        \\  law assoc(x: a, y: a, z: a) {
        \\    always combine(combine(x, y), z) == combine(x, combine(y, z))
        \\  }
        \\}
        \\
        \\pub trait Monoid(a) <= Semigroup(a) {
        \\  fn empty() -> a
        \\  law left_id(x: a) {
        \\    always combine(empty(), x) == x
        \\  }
        \\  law right_id(x: a) {
        \\    always combine(x, empty()) == x
        \\  }
        \\}
        \\
        \\pub default instance sum_u32: Monoid(u32) {
        \\  fn empty() -> u32 { 0u32 }
        \\  fn combine(x: u32, y: u32) -> u32 { x +| y }
        \\}
        \\
        \\pub instance max_u32: Monoid(u32) {
        \\  fn empty() -> u32 { 0u32 }
        \\  fn combine(x: u32, y: u32) -> u32 { max(x, y) }
        \\}
        \\
        \\pub default instance all_bool: Semigroup(bool) {
        \\  fn combine(x: bool, y: bool) -> bool { x && y }
        \\}
        \\
        \\pub instance any_bool: Semigroup(bool) {
        \\  fn combine(x: bool, y: bool) -> bool { x || y }
        \\}
        \\
        \\pub trait Functor(f(_)) {
        \\  fn fmap(fa: f(a), g: fn(a) -> b) -> f(b)
        \\}
        \\
        \\pub trait Applicative(f(_)) <= Functor(f) {
        \\  fn pure(x: a) -> f(a)
        \\  fn ap(ff: f(fn(a) -> b), fa: f(a)) -> f(b)
        \\}
        \\
        \\pub trait Monad(f(_)) <= Applicative(f) {
        \\  fn bind(ma: f(a), k: fn(a) -> f(b)) -> f(b)
        \\  law left_id_m(x: a, k: fn(a) -> f(b)) {
        \\    always bind(pure(x), k) == k(x)
        \\  }
        \\  law right_id_m(m: f(a)) {
        \\    always bind(m, fn(x: a) -> f(a) { pure(x) }) == m
        \\  }
        \\}
        \\
        \\pub default instance opt_monad: Monad(Option) {
        \\  fn pure(x: a) -> Option(a) { Some(x) }
        \\  fn bind(ma: Option(a), k: fn(a) -> Option(b)) -> Option(b) {
        \\    case ma {
        \\      None -> None
        \\      Some(v) -> k(v)
        \\    }
        \\  }
        \\}
        \\
        \\pub fn fold_slice(xs: [a]) -> a with Monoid(a) {
        \\  let mut acc: a = empty()
        \\  for x in xs {
        \\    acc = combine(acc, x)
        \\  }
        \\  acc
        \\}
        \\
        ,
    },
    .{
        .key = "std/option",
        .source =
        \\//// Standard Option helpers for Aethel (rank-1 generic, zero allocator plumbing).
        \\
        \\pub fn is_some(opt: Option(a)) -> bool {
        \\  case opt {
        \\    Some(_) -> true
        \\    None -> false
        \\  }
        \\}
        \\
        \\pub fn is_none(opt: Option(a)) -> bool {
        \\  case opt {
        \\    None -> true
        \\    Some(_) -> false
        \\  }
        \\}
        \\
        \\pub fn unwrap_or(opt: Option(a), fallback: a) -> a {
        \\  case opt {
        \\    Some(v) -> v
        \\    None -> fallback
        \\  }
        \\}
        \\
        \\pub fn map_opt(opt: Option(a), f: fn(a) -> b) -> Option(b) {
        \\  case opt {
        \\    Some(v) -> Some(f(v))
        \\    None -> None
        \\  }
        \\}
        \\
        \\pub fn and_then_opt(opt: Option(a), f: fn(a) -> Option(b)) -> Option(b) {
        \\  case opt {
        \\    Some(v) -> f(v)
        \\    None -> None
        \\  }
        \\}
        \\
        \\pub fn flatten(opt: Option(Option(a))) -> Option(a) {
        \\  case opt {
        \\    Some(inner) -> inner
        \\    None -> None
        \\  }
        \\}
        \\
        \\pub fn or_else(opt: Option(a), alt: Option(a)) -> Option(a) {
        \\  case opt {
        \\    Some(v) -> Some(v)
        \\    None -> alt
        \\  }
        \\}
        \\
        \\pub fn filter(opt: Option(a), pred: fn(a) -> bool) -> Option(a) {
        \\  case opt {
        \\    Some(v) -> if pred(v) { Some(v) } else { None }
        \\    None -> None
        \\  }
        \\}
        \\
        \\pub fn to_result(opt: Option(a), err_val: e) -> Result(a, e) {
        \\  case opt {
        \\    Some(v) -> Ok(v)
        \\    None -> Err(err_val)
        \\  }
        \\}
        \\
        ,
    },
    .{
        .key = "std/result",
        .source =
        \\//// Standard Result helpers for Aethel (rank-1 generic, zero allocator plumbing).
        \\
        \\pub fn is_ok(r: Result(t, e)) -> bool {
        \\  case r {
        \\    Ok(_) -> true
        \\    Err(_) -> false
        \\  }
        \\}
        \\
        \\pub fn is_err(r: Result(t, e)) -> bool {
        \\  case r {
        \\    Err(_) -> true
        \\    Ok(_) -> false
        \\  }
        \\}
        \\
        \\pub fn unwrap_or(r: Result(t, e), fallback: t) -> t {
        \\  case r {
        \\    Ok(v) -> v
        \\    Err(_) -> fallback
        \\  }
        \\}
        \\
        \\pub fn unwrap_err_or(r: Result(t, e), fallback: e) -> e {
        \\  case r {
        \\    Err(e_val) -> e_val
        \\    Ok(_) -> fallback
        \\  }
        \\}
        \\
        \\pub fn map_res(r: Result(t, e), f: fn(t) -> u) -> Result(u, e) {
        \\  case r {
        \\    Ok(v) -> Ok(f(v))
        \\    Err(e_val) -> Err(e_val)
        \\  }
        \\}
        \\
        \\pub fn map_err(r: Result(t, e), f: fn(e) -> f_err) -> Result(t, f_err) {
        \\  case r {
        \\    Ok(v) -> Ok(v)
        \\    Err(e_val) -> Err(f(e_val))
        \\  }
        \\}
        \\
        \\pub fn and_then_res(r: Result(t, e), f: fn(t) -> Result(u, e)) -> Result(u, e) {
        \\  case r {
        \\    Ok(v) -> f(v)
        \\    Err(e_val) -> Err(e_val)
        \\  }
        \\}
        \\
        \\pub fn or_else(r: Result(t, e), alt: Result(t, e)) -> Result(t, e) {
        \\  case r {
        \\    Ok(v) -> Ok(v)
        \\    Err(_) -> alt
        \\  }
        \\}
        \\
        \\pub fn to_option(r: Result(t, e)) -> Option(t) {
        \\  case r {
        \\    Ok(v) -> Some(v)
        \\    Err(_) -> None
        \\  }
        \\}
        \\
        ,
    },
    .{
        .key = "std/math",
        .source =
        \\//// Total, overflow-safe, Lean-verified integer math utilities.
        \\
        \\pub fn abs_i32(x: i32) -> u32 {
        \\  if x < 0i32 {
        \\    (0i64 - (x as i64)) as u32
        \\  } else {
        \\    x as u32
        \\  }
        \\}
        \\
        \\pub fn abs_diff_u32(a: u32, b: u32) -> u32 {
        \\  if a >= b { a -| b } else { b -| a }
        \\}
        \\
        \\pub fn clamp_u32(v: u32, lo: u32, hi: u32) -> u32 {
        \\  if v < lo {
        \\    lo
        \\  } else if v > hi {
        \\    hi
        \\  } else {
        \\    v
        \\  }
        \\}
        \\
        \\pub fn clamp_i32(v: i32, lo: i32, hi: i32) -> i32 {
        \\  if v < lo {
        \\    lo
        \\  } else if v > hi {
        \\    hi
        \\  } else {
        \\    v
        \\  }
        \\}
        \\
        \\pub fn gcd_u32(a_in: u32, b_in: u32) -> u32 {
        \\  let mut a: u32 = a_in
        \\  let mut b: u32 = b_in
        \\  while b > 0u32 {
        \\    let rem = a % b
        \\    a = b
        \\    b = rem
        \\  }
        \\  a
        \\}
        \\
        \\pub fn pow_u32(base: u32, exp: u32) -> u32 decreases exp {
        \\  if exp == 0u32 {
        \\    1u32
        \\  } else {
        \\    base *% pow_u32(base, exp - 1u32)
        \\  }
        \\}
        \\
        \\law abs_diff_sym(a: u8, b: u8) {
        \\  always abs_diff_u32(a as u32, b as u32) == abs_diff_u32(b as u32, a as u32)
        \\}
        \\
        \\law clamp_upper(v: u8, hi: u8) {
        \\  always clamp_u32(v as u32, 0u32, hi as u32) <= (hi as u32)
        \\}
        \\
        ,
    },
    .{
        .key = "std/str",
        .source =
        \\//// Standard string helpers for Aethel (immutable copyable slices).
        \\//// Core operations (`str.len`, `str.is_empty`, `str.eq`, `str.concat`,
        \\//// `str.starts_with`, `str.ends_with`, `str.contains`, `str.byte_at`,
        \\//// `str.slice_bytes`) are lowered directly by the compiler backend.
        \\
        \\pub fn empty() -> String {
        \\  ""
        \\}
        \\
        ,
    },
    .{
        .key = "std/io",
        .source =
        \\//// Standard I/O module for Aethel (`io.println`, `io.print`, `io.eprintln`, `io.eprint`).
        \\//// Lowered directly to OS stdio buffered writers by the compiler runtime.
        \\
        \\pub fn noop() {
        \\}
        \\
        ,
    },
    .{
        .key = "std/vec",
        .source =
        \\//// Layout-polymorphic, borrow-checked dynamic array (`Vec(T)`).
        \\////
        \\//// Zero user-facing allocator arguments: allocation, Perceus in-place reuse
        \\//// (`len < cap`), physical layout selection (`@layout(soa)`, `@layout(aosoa(W))`,
        \\//// `@layout(auto)`), reallocation safety (`Unreserved`), and deterministic
        \\//// scope-exit reclamation are enforced automatically by the compiler and Lean gate.
        \\////
        \\//// Intrinsics exposed via `import std/vec [as vec]`:
        \\////   vec.new() / vec.with_capacity(cap) / vec.len(v) / vec.capacity(v)
        \\////   vec.is_empty(v) / vec.push(v, x) / vec.pop(v) / vec.get(v, i)
        \\////   vec.set(v, i, x) / vec.swap_remove(v, i) / vec.reserve(v, add)
        \\////   vec.clear(v) / vec.as_slice(v) / vec.as_collection(v)
        \\
        \\pub fn initial_capacity() -> u64 {
        \\  8u64
        \\}
        \\
        ,
    },
    .{
        .key = "std/map",
        .source =
        \\//// SwissTable-style SoA hash map (`Map(K, V)`), zero allocator plumbing.
        \\////
        \\//// Physical representation separates 64B-aligned 1-byte `ctrl` (`h2` fingerprint)
        \\//// slots from dense `keys` and `vals` columns, capping load factor at 7/8
        \\//// (`used * 8 <= cap * 7`), verified in `Aethel.StdContainers`.
        \\////
        \\//// Intrinsics exposed via `import std/map [as map]`:
        \\////   map.new() / map.with_capacity(cap) / map.len(m) / map.is_empty(m)
        \\////   map.insert(m, k, v) / map.put(m, k, v) / map.get(m, k)
        \\////   map.contains(m, k) / map.remove(m, k) / map.clear(m)
        \\
        \\pub fn load_factor_numerator() -> u32 {
        \\  7u32
        \\}
        \\
        \\pub fn load_factor_denominator() -> u32 {
        \\  8u32
        \\}
        \\
        ,
    },
    .{
        .key = "std/set",
        .source =
        \\//// SwissTable-style SoA hash set (`Set(T)`), zero allocator plumbing.
        \\////
        \\//// Backed by 64B-aligned 1-byte `ctrl` (`h2` fingerprint) slots and dense
        \\//// key storage (`Aethel.StdContainers`), borrow-checked across mutation.
        \\////
        \\//// Intrinsics exposed via `import std/set [as set]`:
        \\////   set.new() / set.with_capacity(cap) / set.len(s) / set.is_empty(s)
        \\////   set.insert(s, x) / set.contains(s, x) / set.remove(s, x) / set.clear(s)
        \\
        \\pub fn empty_count() -> u64 {
        \\  0u64
        \\}
        \\
        ,
    },
    .{
        .key = "std/deque",
        .source =
        \\//// Double-ended ring-buffer queue (`Deque(T)`), zero allocator plumbing.
        \\////
        \\//// Uses power-of-two capacity modular indexing `(head + idx) % cap` verified
        \\//// injective in `Aethel.StdContainers` and automatic scope-exit drop.
        \\////
        \\//// Intrinsics exposed via `import std/deque [as deque]`:
        \\////   deque.new() / deque.with_capacity(cap) / deque.len(d) / deque.is_empty(d)
        \\////   deque.push_back(d, x) / deque.push_front(d, x)
        \\////   deque.pop_front(d) / deque.pop_back(d) / deque.get(d, i) / deque.clear(d)
        \\
        \\pub fn empty_count() -> u64 {
        \\  0u64
        \\}
        \\
        ,
    },
};

pub fn lookup(key: []const u8) ?[:0]const u8 {
    for (modules) |m| {
        if (std.mem.eql(u8, m.key, key)) return m.source;
    }
    return null;
}
