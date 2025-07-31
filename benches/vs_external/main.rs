//! Benchmark the crate's implementation vs external software implementations of posits and
//! floats in C.
//!
//! In order to run these tests, you need the `softfloat` and `softposit` C libraries available to
//! the linker (e.g. using the `-L` rustc option if you don't have them in the standard paths).
//!
//! Sources for external libraries:
//!   - https://www.jhauser.us/arithmetic/SoftFloat.html
//!   - https://gitlab.com/cerlane/SoftPosit

use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use soft_posit::{p32, p64};

mod cerlane_softposit;
mod berkeley_softfloat;

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

/// Benchmark this number of operations
const LEN: usize = 1 << 20;

/// Generate arrays of random floats/posits and benchmark our impl and external impls in adding
/// pairs of numbers.
fn add_32(c: &mut Criterion) {
  let data_float = arr::<{LEN * 2}, _>(rand_f32);
  let data_posit = arr::<{LEN * 2}, _>(rand_p32);

  let mut g = c.benchmark_group("add_32");
  g.throughput(Throughput::Elements(LEN as u64));
  g.bench_function("softfloat", |b| b.iter(|| {
    for &[x, y] in data_float.as_chunks().0 {
      unsafe { berkeley_softfloat::f32_add(black_box(x.into()), black_box(y.into())) };
    }
  }));
  g.bench_function("softposit", |b| b.iter(|| {
    for &[x, y] in data_posit.as_chunks().0 {
      unsafe { cerlane_softposit::p32_add(black_box(x.into()), black_box(y.into())) };
    }
  }));
  g.bench_function("posit", |b| b.iter(|| {
    for &[x, y] in data_posit.as_chunks().0 {
      p32::add(black_box(x), black_box(y));
    }
  }));
  g.finish();
}

/// Generate arrays of random floats/posits and benchmark our impl and external impls in adding
/// pairs of numbers.
fn add_64(c: &mut Criterion) {
  let data_float = arr::<{LEN * 2}, _>(rand_f64);
  let data_posit = arr::<{LEN * 2}, _>(rand_p64);

  let mut g = c.benchmark_group("add_64");
  g.throughput(Throughput::Elements(LEN as u64));
  g.bench_function("softfloat", |b| b.iter(|| {
    for &[x, y] in data_float.as_chunks().0 {
      unsafe { berkeley_softfloat::f64_add(black_box(x.into()), black_box(y.into())) };
    }
  }));
  /*g.bench_function("softposit", |b| b.iter(|| {
    for &[x, y] in data_posit.as_chunks().0 {
      unsafe { p64_add(black_box(x.into()), black_box(y.into())) };
    }
  }));*/
  g.bench_function("posit", |b| b.iter(|| {
    for &[x, y] in data_posit.as_chunks().0 {
      p64::add(black_box(x), black_box(y));
    }
  }));
  g.finish();
}

criterion_group!(add,
  add_32,
  add_64,
);

criterion_main!(add);
