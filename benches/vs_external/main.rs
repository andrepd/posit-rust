//! Benchmark the crate's implementation vs external software implementations of posits and
//! floats in C.
//!
//! In order to run these tests, you need the `softfloat` and `softposit` C libraries available to
//! the linker (e.g. using the `-L` rustc option if you don't have them in the standard paths).
//!
//! Sources for external libraries:
//!   - https://www.jhauser.us/arithmetic/SoftFloat.html
//!   - https://gitlab.com/cerlane/SoftPosit
//!   - https://github.com/stillwater-sc/universal/

use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use fast_posit::{p32, p64, q32};

//

#[cfg(feature = "cerlane-softposit")]
mod cerlane_softposit;

#[cfg(feature = "berkeley-softfloat")]
mod berkeley_softfloat;

#[cfg(feature = "stillwater-softposit")]
mod stillwater_softposit;

/// Create an array of `n` [`p32`]s and an array of `n` [`f32`]s. The values of the float array
/// are the values of the posit array, rounded.
fn make_data_32(n: usize) -> (Box<[p32]>, Box<[f32]>) {
  use fast_posit::RoundFrom;
  let rand = || p32::from_bits(rand::random_range(i32::MIN + 1 ..= i32::MAX));
  let posits: Vec<_> = (0..n).map(|_| rand()).collect();
  let floats: Vec<_> = posits.iter().map(|&p| f32::round_from(p)).collect();
  (posits.into_boxed_slice(), floats.into_boxed_slice())
}

/// Create an array of `n` [`p64`]s and an array of `n` [`f64`]s. The values of the float array
/// are the values of the posit array, rounded.
fn make_data_64(n: usize) -> (Box<[p64]>, Box<[f64]>) {
  use fast_posit::RoundFrom;
  let rand = || p64::from_bits(rand::random_range(i64::MIN + 1 ..= i64::MAX));
  let posits: Vec<_> = (0..n).map(|_| rand()).collect();
  let floats: Vec<_> = posits.iter().map(|&p| f64::round_from(p)).collect();
  (posits.into_boxed_slice(), floats.into_boxed_slice())
}

/// Benchmark a 2-arg function
fn bench_2ary<T: Copy, U: From<T>>(
  g: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
  name: &str,
  data: &[T],
  mut f: impl FnMut(U, U) -> U,
) {
  assert!(data.len() % 2 == 0, "Cannot benchmark 2-ary function with odd number of elements");
  g.throughput(Throughput::Elements(data.len() as u64 / 2));
  g.bench_function(name, |b| b.iter(|| {
    for &[x, y] in data.as_chunks().0 {
      let _ = black_box(f(black_box(U::from(x)), black_box(U::from(y))));
    }
  }));
}

/// Benchmark a 1-arg function
fn bench_1ary<T: Copy, U: From<T>>(
  g: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
  name: &str,
  data: &[T],
  mut f: impl FnMut(U) -> U,
) {
  g.throughput(Throughput::Elements(data.len() as u64));
  g.bench_function(name, |b| b.iter(|| {
    for &x in data {
      let _ = black_box(f(black_box(U::from(x))));
    }
  }));
}

/// Benchmark a 1-arg function that accumulates into another type.
fn bench_1ary_accumulate<T: Copy, A: Clone, U: From<T>>(
  g: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
  name: &str,
  initial: A,
  data: &[T],
  mut f: impl FnMut(&mut A, U),
) {
  g.throughput(Throughput::Elements(data.len() as u64));
  g.bench_function(name, |b| b.iter(|| {
    let mut accum = black_box(initial.clone());
    for &x in data {
      let _ = black_box(f(&mut accum, black_box(U::from(x))));
    }
  }));
}

//

/// Benchmark this number of operations
const LEN: usize = 1 << 20;

/// Generate arrays of random floats/posits and benchmark our impl and external impls in adding
/// pairs of numbers.
fn add_32(c: &mut Criterion) {
  let (data_posit, data_float) = make_data_32(LEN * 2);
  let mut g = c.benchmark_group("add_32");

  #[cfg(feature = "berkeley-softfloat")]
  bench_2ary(&mut g, "berkeley-softfloat", &data_float, |x, y| unsafe { berkeley_softfloat::f32_add(x, y) });

  #[cfg(feature = "cerlane-softposit")]
  bench_2ary(&mut g, "cerlane-softposit", &data_posit, |x, y| unsafe { cerlane_softposit::p32_add(x, y) });

  #[cfg(feature = "stillwater-softposit")]
  bench_2ary(&mut g, "stillwater-softposit", &data_posit, |x, y| unsafe { stillwater_softposit::posit32_addp32(x, y) });

  bench_2ary(&mut g, "posit", &data_posit, |x: p32, y: p32| x + y);

  g.finish();
}

/// Generate arrays of random floats/posits and benchmark our impl and external impls in
/// multiplying pairs of numbers.
fn mul_32(c: &mut Criterion) {
  let (data_posit, data_float) = make_data_32(LEN * 2);
  let mut g = c.benchmark_group("mul_32");

  #[cfg(feature = "berkeley-softfloat")]
  bench_2ary(&mut g, "berkeley-softfloat", &data_float, |x, y| unsafe { berkeley_softfloat::f32_mul(x, y) });

  #[cfg(feature = "cerlane-softposit")]
  bench_2ary(&mut g, "cerlane-softposit", &data_posit, |x, y| unsafe { cerlane_softposit::p32_mul(x, y) });

  #[cfg(feature = "stillwater-softposit")]
  bench_2ary(&mut g, "stillwater-softposit", &data_posit, |x, y| unsafe { stillwater_softposit::posit32_mulp32(x, y) });

  bench_2ary(&mut g, "posit", &data_posit, |x: p32, y: p32| x * y);

  g.finish();
}

/// Generate arrays of random floats/posits and benchmark our impl and external impls in dividing
/// pairs of numbers.
fn div_32(c: &mut Criterion) {
  let (data_posit, data_float) = make_data_32(LEN * 2);
  let mut g = c.benchmark_group("div_32");

  #[cfg(feature = "berkeley-softfloat")]
  bench_2ary(&mut g, "berkeley-softfloat", &data_float, |x, y| unsafe { berkeley_softfloat::f32_div(x, y) });

  #[cfg(feature = "cerlane-softposit")]
  bench_2ary(&mut g, "cerlane-softposit", &data_posit, |x, y| unsafe { cerlane_softposit::p32_div(x, y) });

  #[cfg(feature = "stillwater-softposit")]
  bench_2ary(&mut g, "stillwater-softposit", &data_posit, |x, y| unsafe { stillwater_softposit::posit32_divp32(x, y) });

  bench_2ary(&mut g, "posit", &data_posit, |x: p32, y: p32| x / y);

  g.finish();
}

/// Generate arrays of random floats/posits and benchmark our impl and external impls in
/// calculating the square roots.
fn sqrt_32(c: &mut Criterion) {
  let (data_posit, data_float) = make_data_32(LEN);
  let mut g = c.benchmark_group("sqrt_32");

  #[cfg(feature = "berkeley-softfloat")]
  bench_1ary(&mut g, "berkeley-softfloat", &data_float, |x| unsafe { berkeley_softfloat::f32_sqrt(x) });

  #[cfg(feature = "cerlane-softposit")]
  bench_1ary(&mut g, "cerlane-softposit", &data_posit, |x| unsafe { cerlane_softposit::p32_sqrt(x) });

  #[cfg(feature = "stillwater-softposit")]
  bench_1ary(&mut g, "stillwater-softposit", &data_posit, |x| unsafe { stillwater_softposit::posit32_sqrt(x) });

  bench_1ary(&mut g, "posit", &data_posit, |x: p32| x.sqrt());

  g.finish();
}

/// Generate arrays of random floats/posits and benchmark our impl and external impls in adding
/// pairs of numbers.
fn add_64(c: &mut Criterion) {
  let (data_posit, data_float) = make_data_64(LEN * 2);
  let mut g = c.benchmark_group("add_64");

  #[cfg(feature = "berkeley-softfloat")]
  bench_2ary(&mut g, "berkeley-softfloat", &data_float, |x, y| unsafe { berkeley_softfloat::f64_add(x, y) });

  /*#[cfg(feature = "cerlane-softposit")]
  bench_2ary(&mut g, "cerlane-softposit", &data_posit, |x, y| unsafe { cerlane_softposit::p64_add(x, y) };*/

  #[cfg(feature = "stillwater-softposit")]
  bench_2ary(&mut g, "stillwater-softposit", &data_posit, |x, y| unsafe { stillwater_softposit::posit64_addp64(x, y) });

  bench_2ary(&mut g, "posit", &data_posit, |x: p64, y: p64| x + y);

  g.finish();
}

/// Generate arrays of random floats/posits and benchmark our impl and external impls in
/// multiplying pairs of numbers.
fn mul_64(c: &mut Criterion) {
  let (data_posit, data_float) = make_data_64(LEN * 2);
  let mut g = c.benchmark_group("mul_64");

  #[cfg(feature = "berkeley-softfloat")]
  bench_2ary(&mut g, "berkeley-softfloat", &data_float, |x, y| unsafe { berkeley_softfloat::f64_mul(x, y) });

  /*#[cfg(feature = "cerlane-softposit")]
  bench_2ary(&mut g, "cerlane-softposit", &data_posit, |x, y| unsafe { cerlane_softposit::p64_mul(x, y) };*/

  #[cfg(feature = "stillwater-softposit")]
  bench_2ary(&mut g, "stillwater-softposit", &data_posit, |x, y| unsafe { stillwater_softposit::posit64_mulp64(x, y) });

  bench_2ary(&mut g, "posit", &data_posit, |x: p64, y: p64| x * y);

  g.finish();
}

/// Generate arrays of random floats/posits and benchmark our impl and external impls in dividing
/// pairs of numbers.
fn div_64(c: &mut Criterion) {
  let (data_posit, data_float) = make_data_64(LEN * 2);
  let mut g = c.benchmark_group("div_64");

  #[cfg(feature = "berkeley-softfloat")]
  bench_2ary(&mut g, "berkeley-softfloat", &data_float, |x, y| unsafe { berkeley_softfloat::f64_div(x, y) });

  /*#[cfg(feature = "cerlane-softposit")]
  bench_2ary(&mut g, "cerlane-softposit", &data_posit, |x, y| unsafe { cerlane_softposit::p64_div(x, y) };*/

  #[cfg(feature = "stillwater-softposit")]
  bench_2ary(&mut g, "stillwater-softposit", &data_posit, |x, y| unsafe { stillwater_softposit::posit64_divp64(x, y) });

  bench_2ary(&mut g, "posit", &data_posit, |x: p64, y: p64| x / y);

  g.finish();
}

/// Generate arrays of random floats/posits and benchmark our impl and external impls in
/// calculating the square roots.
fn sqrt_64(c: &mut Criterion) {
  let (data_posit, data_float) = make_data_64(LEN);
  let mut g = c.benchmark_group("sqrt_64");

  #[cfg(feature = "berkeley-softfloat")]
  bench_1ary(&mut g, "berkeley-softfloat", &data_float, |x| unsafe { berkeley_softfloat::f64_sqrt(x) });

  /*#[cfg(feature = "cerlane-softposit")]
  bench_1ary(&mut g, "cerlane-softposit", &data_posit, |x| unsafe { cerlane_softposit::p64_sqrt(x) });*/

  #[cfg(feature = "stillwater-softposit")]
  bench_1ary(&mut g, "stillwater-softposit", &data_posit, |x| unsafe { stillwater_softposit::posit64_sqrt(x) });

  bench_1ary(&mut g, "posit", &data_posit, |x: p64| x.sqrt());

  g.finish();
}

/// Generate arrays of random posits and benchmark our impl and external impls in summing them all
/// into a quire.
fn quire_add_32(c: &mut Criterion) {
  let (data_posit, _) = make_data_32(LEN);
  let mut g = c.benchmark_group("quire_add_32");

  #[cfg(feature = "cerlane-softposit")]
  bench_1ary_accumulate(
    &mut g,
    "cerlane-softposit",
    cerlane_softposit::quire32_t::default(),
    &data_posit,
    |q, x| unsafe { *q = cerlane_softposit::q32_add(*q, x) },
  );

  bench_1ary_accumulate(
    &mut g,
    "posit",
    q32::ZERO,
    &data_posit,
    |q: &mut q32, x: p32| *q += x,
  );

  g.finish();
}

criterion_group!(add,
  add_32,
  add_64,
);

criterion_group!(mul,
  mul_32,
  mul_64,
);

criterion_group!(div,
  div_32,
  div_64,
);

criterion_group!(sqrt,
  sqrt_32,
  sqrt_64,
);

criterion_group!(quire,
  quire_add_32,
);

criterion_main!(add, mul, div, sqrt, quire);
