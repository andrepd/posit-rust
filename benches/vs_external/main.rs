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
use soft_posit::{p32, p64};

//

#[cfg(feature = "cerlane-softposit")]
mod cerlane_softposit;

#[cfg(feature = "berkeley-softfloat")]
mod berkeley_softfloat;

#[cfg(feature = "stillwater-softposit")]
mod stillwater_softposit;

fn rand_f32() -> f32 {
  rand::random_range(-1e30 ..= 1e30)
}

fn rand_f64() -> f64 {
  rand::random_range(-1e60 ..= 1e60)
}

fn rand_p32() -> p32 {
  p32::from_bits(rand::random_range(i32::MIN + 1 ..= i32::MAX))
}

fn rand_p64() -> p64 {
  p64::from_bits(rand::random_range(i64::MIN + 1 ..= i64::MAX))
}

fn arr<const N: usize, T: Default + Copy>(mut f: impl FnMut() -> T) -> Box<[T; N]> {
  let mut arr = Box::new([T::default(); N]);
  for i in arr.as_mut_slice() { *i = f() }
  arr
}

/// Benchmark a 2-arg function
fn bench_2ary<T: Copy, const N: usize, U: From<T>>(
  g: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
  name: &str,
  data: &[T; N],
  mut f: impl FnMut(U, U) -> U,
) {
  const { assert!(N & 1 == 0, "Cannot benchmark 2-ary function with odd number of elements") };
  g.throughput(Throughput::Elements(N as u64 / 2));
  g.bench_function(name, |b| b.iter(|| {
    for &[x, y] in data.as_chunks().0 {
      f(black_box(U::from(x)), black_box(U::from(y)));
    }
  }));
}

//

/// Benchmark this number of operations
const LEN: usize = 1 << 20;

/// Generate arrays of random floats/posits and benchmark our impl and external impls in adding
/// pairs of numbers.
fn add_32(c: &mut Criterion) {
  let data_float = arr::<{LEN * 2}, _>(rand_f32);
  let data_posit = arr::<{LEN * 2}, _>(rand_p32);
  let mut g = c.benchmark_group("add_32");

  #[cfg(feature = "berkeley-softfloat")]
  let _ = bench_2ary(&mut g, "berkeley-softfloat", &data_float, |x, y| unsafe { berkeley_softfloat::f32_add(x, y) });

  #[cfg(feature = "cerlane-softposit")]
  let _ = bench_2ary(&mut g, "cerlane-softposit", &data_posit, |x, y| unsafe { cerlane_softposit::p32_add(x, y) });

  #[cfg(feature = "stillwater-softposit")]
  let _ = bench_2ary(&mut g, "stillwater-softposit", &data_posit, |x, y| unsafe { stillwater_softposit::posit32_addp32(x, y) });

  let _ = bench_2ary(&mut g, "posit", &data_posit, |x: p32, y: p32| x + y);

  g.finish();
}

/// Generate arrays of random floats/posits and benchmark our impl and external impls in adding
/// pairs of numbers.
fn add_64(c: &mut Criterion) {
  let data_float = arr::<{LEN * 2}, _>(rand_f64);
  let data_posit = arr::<{LEN * 2}, _>(rand_p64);
  let mut g = c.benchmark_group("add_64");

  #[cfg(feature = "berkeley-softfloat")]
  let _ = bench_2ary(&mut g, "berkeley-softfloat", &data_float, |x, y| unsafe { berkeley_softfloat::f64_add(x, y) });

  /*#[cfg(feature = "cerlane-softposit")]
  let _ = bench_2ary(&mut g, "cerlane-softposit", &data_posit, |x, y| unsafe { cerlane_softposit::p64_add(x, y) };*/

  #[cfg(feature = "stillwater-softposit")]
  let _ = bench_2ary(&mut g, "stillwater-softposit", &data_posit, |x, y| unsafe { stillwater_softposit::posit64_addp64(x, y) });

  let _ = bench_2ary(&mut g, "posit", &data_posit, |x: p64, y: p64| x + y);

  g.finish();
}

criterion_group!(add,
  add_32,
  add_64,
);

criterion_main!(add);
