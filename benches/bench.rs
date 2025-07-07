use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use soft_posit::{p32, p64};

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
  for num in NUMS_32 {
    let dec = unsafe { num.bench_decode_regular() };
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}", num.to_bits())), &num, |b, &num| {
      b.iter(|| unsafe { black_box(dec).bench_encode_regular() } );
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
  for num in NUMS_64 {
    let dec = unsafe { num.bench_decode_regular() };
    g.throughput(Throughput::Elements(1));
    g.bench_with_input(BenchmarkId::from_parameter(format_args!("0b{:032b}", num.to_bits())), &num, |b, &num| {
      b.iter(|| unsafe { black_box(dec).bench_encode_regular() } );
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

criterion_main!(baseline_fpu, decode, encode);
