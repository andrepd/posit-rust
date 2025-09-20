use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use fast_posit::{p32, p64, q32, q64};

// Establish a baseline by comparing with a single fpu add

fn baseline_fpu_add_f32(c: &mut Criterion) {
  c.bench_function("baseline_fpu_add_f32", |b| {
    b.iter(|| black_box(3.14) + black_box(69.420));
  });
}

fn baseline_fpu_add_f64(c: &mut Criterion) {
  c.bench_function("baseline_fpu_add_f64", |b| {
    b.iter(|| black_box(3.14) + black_box(69.420));
  });
}

// Time decoding 1 posit

const NUMS_32: [p32; 4] = [
  unsafe { p32::from_bits_unchecked(0b00101011100101110110111101100011u32 as _) },
  unsafe { p32::from_bits_unchecked(0b00000000010101010100111100100101u32 as _) },
  unsafe { p32::from_bits_unchecked(0b11010100001001010100101000101110u32 as _) },
  unsafe { p32::from_bits_unchecked(0b01110010011111001111001001110000u32 as _) },
];

fn decode_p32(c: &mut Criterion) {
  let mut g = c.benchmark_group("decode_p32");
  for num in NUMS_32 {
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}", num.to_bits())), &num, |b, &num| {
      b.iter(|| unsafe { black_box(num).bench_decode_regular() } );
    });
  }
  g.finish();
}

fn encode_p32(c: &mut Criterion) {
  let mut g = c.benchmark_group("encode_p32");
  for (i, num) in NUMS_32.iter().enumerate() {
    let dec = unsafe { num.bench_decode_regular() };
    let sticky = i as i32 % 2;
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}", num.to_bits())), &num, |b, &num| {
      b.iter(|| unsafe { black_box(dec).bench_encode_regular_round(black_box(sticky)) } );
    });
  }
  g.finish();
}

fn add_kernel_p32(c: &mut Criterion) {
  let mut g = c.benchmark_group("add_kernel_p32");
  for (x, y) in NUMS_32.iter().zip(NUMS_32.iter().skip(1)) {
    let x_dec = unsafe { x.bench_decode_regular() };
    let y_dec = unsafe { y.bench_decode_regular() };
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}/0b{:032b}", x.to_bits(), y.to_bits())), &(x_dec, y_dec), |b, &(x, y)| {
      b.iter(|| unsafe { p32::bench_add_kernel(black_box(x), black_box(y)) } );
    });
  }
  g.finish();
}

fn mul_kernel_p32(c: &mut Criterion) {
  let mut g = c.benchmark_group("mul_kernel_p32");
  for (x, y) in NUMS_32.iter().zip(NUMS_32.iter().skip(1)) {
    let x_dec = unsafe { x.bench_decode_regular() };
    let y_dec = unsafe { y.bench_decode_regular() };
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}/0b{:032b}", x.to_bits(), y.to_bits())), &(x_dec, y_dec), |b, &(x, y)| {
      b.iter(|| unsafe { p32::bench_mul_kernel(black_box(x), black_box(y)) } );
    });
  }
  g.finish();
}

fn div_kernel_p32(c: &mut Criterion) {
  let mut g = c.benchmark_group("div_kernel_p32");
  for (x, y) in NUMS_32.iter().zip(NUMS_32.iter().skip(1)) {
    let x_dec = unsafe { x.bench_decode_regular() };
    let y_dec = unsafe { y.bench_decode_regular() };
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}/0b{:032b}", x.to_bits(), y.to_bits())), &(x_dec, y_dec), |b, &(x, y)| {
      b.iter(|| unsafe { p32::bench_div_kernel(black_box(x), black_box(y)) } );
    });
  }
  g.finish();
}

fn add_p32(c: &mut Criterion) {
  let mut g = c.benchmark_group("add_p32");
  for (&x, &y) in NUMS_32.iter().zip(NUMS_32.iter().skip(1)) {
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}/0b{:032b}", x.to_bits(), y.to_bits())), &(x, y), |b, &(x, y)| {
      b.iter(|| black_box(x) + black_box(y) );
    });
  }
  g.finish();
}

fn sub_p32(c: &mut Criterion) {
  let mut g = c.benchmark_group("sub_p32");
  for (&x, &y) in NUMS_32.iter().zip(NUMS_32.iter().skip(1)) {
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}/0b{:032b}", x.to_bits(), y.to_bits())), &(x, y), |b, &(x, y)| {
      b.iter(|| black_box(x) - black_box(y) );
    });
  }
  g.finish();
}

fn mul_p32(c: &mut Criterion) {
  let mut g = c.benchmark_group("mul_p32");
  for (&x, &y) in NUMS_32.iter().zip(NUMS_32.iter().skip(1)) {
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}/0b{:032b}", x.to_bits(), y.to_bits())), &(x, y), |b, &(x, y)| {
      b.iter(|| black_box(x) * black_box(y) );
    });
  }
  g.finish();
}

fn div_p32(c: &mut Criterion) {
  let mut g = c.benchmark_group("div_p32");
  for (&x, &y) in NUMS_32.iter().zip(NUMS_32.iter().skip(1)) {
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}/0b{:032b}", x.to_bits(), y.to_bits())), &(x, y), |b, &(x, y)| {
      b.iter(|| black_box(x) / black_box(y) );
    });
  }
  g.finish();
}

fn quire_add_p32(c: &mut Criterion) {
  let mut g = c.benchmark_group("quire_add_p32");
  for num in NUMS_32 {
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}", num.to_bits())), &num, |b, &num| {
      b.iter(|| { let mut q = q32::ZERO; q += black_box(num) });
    });
  }
  g.finish();
}

const NUMS_64: [p64; 4] = [
  unsafe { p64::from_bits_unchecked(0b0010101110010111011011110110001100101001101111011111000111100111u64 as _) },
  unsafe { p64::from_bits_unchecked(0b0000000001010101010011110010010100011000100101110110100010000011u64 as _) },
  unsafe { p64::from_bits_unchecked(0b1101010000100101010010100010111011010010011010111001111111001011u64 as _) },
  unsafe { p64::from_bits_unchecked(0b0111001001111100111100100111000011010111000101000001001101001111u64 as _) },
];

fn decode_p64(c: &mut Criterion) {
  let mut g = c.benchmark_group("decode_p64");
  for num in NUMS_64 {
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}", num.to_bits())), &num, |b, &num| {
      b.iter(|| unsafe { black_box(num).bench_decode_regular() } );
    });
  }
  g.finish();
}

fn encode_p64(c: &mut Criterion) {
  let mut g = c.benchmark_group("encode_p64");
  for (i, num) in NUMS_64.iter().enumerate() {
    let dec = unsafe { num.bench_decode_regular() };
    let sticky = i as i64 % 2;
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}", num.to_bits())), &num, |b, &num| {
      b.iter(|| unsafe { black_box(dec).bench_encode_regular_round(black_box(sticky)) } );
    });
  }
  g.finish();
}

fn add_kernel_p64(c: &mut Criterion) {
  let mut g = c.benchmark_group("add_kernel_p64");
  for (x, y) in NUMS_64.iter().zip(NUMS_64.iter().skip(1)) {
    let x_dec = unsafe { x.bench_decode_regular() };
    let y_dec = unsafe { y.bench_decode_regular() };
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:064b}/0b{:064b}", x.to_bits(), y.to_bits())), &(x_dec, y_dec), |b, &(x, y)| {
      b.iter(|| unsafe { p64::bench_add_kernel(black_box(x), black_box(y)) } );
    });
  }
  g.finish();
}

fn mul_kernel_p64(c: &mut Criterion) {
  let mut g = c.benchmark_group("mul_kernel_p64");
  for (x, y) in NUMS_64.iter().zip(NUMS_64.iter().skip(1)) {
    let x_dec = unsafe { x.bench_decode_regular() };
    let y_dec = unsafe { y.bench_decode_regular() };
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:064b}/0b{:064b}", x.to_bits(), y.to_bits())), &(x_dec, y_dec), |b, &(x, y)| {
      b.iter(|| unsafe { p64::bench_mul_kernel(black_box(x), black_box(y)) } );
    });
  }
  g.finish();
}

fn div_kernel_p64(c: &mut Criterion) {
  let mut g = c.benchmark_group("div_kernel_p64");
  for (x, y) in NUMS_64.iter().zip(NUMS_64.iter().skip(1)) {
    let x_dec = unsafe { x.bench_decode_regular() };
    let y_dec = unsafe { y.bench_decode_regular() };
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:064b}/0b{:064b}", x.to_bits(), y.to_bits())), &(x_dec, y_dec), |b, &(x, y)| {
      b.iter(|| unsafe { p64::bench_div_kernel(black_box(x), black_box(y)) } );
    });
  }
  g.finish();
}

fn add_p64(c: &mut Criterion) {
  let mut g = c.benchmark_group("add_p64");
  for (&x, &y) in NUMS_64.iter().zip(NUMS_64.iter().skip(1)) {
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:064b}/0b{:064b}", x.to_bits(), y.to_bits())), &(x, y), |b, &(x, y)| {
      b.iter(|| black_box(x) + black_box(y) );
    });
  }
  g.finish();
}

fn sub_p64(c: &mut Criterion) {
  let mut g = c.benchmark_group("sub_p64");
  for (&x, &y) in NUMS_64.iter().zip(NUMS_64.iter().skip(1)) {
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:064b}/0b{:064b}", x.to_bits(), y.to_bits())), &(x, y), |b, &(x, y)| {
      b.iter(|| black_box(x) - black_box(y) );
    });
  }
  g.finish();
}

fn mul_p64(c: &mut Criterion) {
  let mut g = c.benchmark_group("mul_p64");
  for (&x, &y) in NUMS_64.iter().zip(NUMS_64.iter().skip(1)) {
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:064b}/0b{:064b}", x.to_bits(), y.to_bits())), &(x, y), |b, &(x, y)| {
      b.iter(|| black_box(x) * black_box(y) );
    });
  }
  g.finish();
}

fn div_p64(c: &mut Criterion) {
  let mut g = c.benchmark_group("div_p64");
  for (&x, &y) in NUMS_64.iter().zip(NUMS_64.iter().skip(1)) {
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:064b}/0b{:064b}", x.to_bits(), y.to_bits())), &(x, y), |b, &(x, y)| {
      b.iter(|| black_box(x) / black_box(y) );
    });
  }
  g.finish();
}

fn quire_add_p64(c: &mut Criterion) {
  let mut g = c.benchmark_group("quire_add_p64");
  for num in NUMS_64 {
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}", num.to_bits())), &num, |b, &num| {
      b.iter(|| { let mut q = q64::ZERO; q += black_box(num) });
    });
  }
  g.finish();
}

criterion_group!(baseline_fpu,
  baseline_fpu_add_f32,
  baseline_fpu_add_f64,
);

criterion_group!(decode,
  decode_p32,
  decode_p64,
);

criterion_group!(encode,
  encode_p32,
  encode_p64,
);

criterion_group!(add,
  add_kernel_p32,
  add_kernel_p64,
  add_p32,
  add_p64,
  sub_p32,
  sub_p64,
);

criterion_group!(mul,
  mul_kernel_p32,
  mul_kernel_p64,
  mul_p32,
  mul_p64,
);

criterion_group!(div,
  div_kernel_p32,
  div_kernel_p64,
  div_p32,
  div_p64,
);

criterion_group!(quire,
  quire_add_p32,
  quire_add_p64,
);

criterion_main!(baseline_fpu, decode, encode, add, mul, div, quire);
