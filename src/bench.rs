//! Re-export some internals for benchmarking purposes; available with feature = "bench".

use crate::posit::{Posit, Decoded};

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  pub unsafe fn bench_decode_regular(self) -> Decoded<N, ES, Int> {
    unsafe { self.decode_regular() }
  }

  pub unsafe fn bench_add_kernel(a: Decoded<N, ES, Int>, b: Decoded<N, ES, Int>) -> (Decoded<N, ES, Int>, Int) {
    unsafe { Self::add_kernel(a, b) }
  }

  pub unsafe fn bench_mul_kernel(a: Decoded<N, ES, Int>, b: Decoded<N, ES, Int>) -> (Decoded<N, ES, Int>, Int) {
    unsafe { Self::mul_kernel(a, b) }
  }

  pub unsafe fn bench_div_kernel(a: Decoded<N, ES, Int>, b: Decoded<N, ES, Int>) -> (Decoded<N, ES, Int>, Int) {
    unsafe { Self::div_kernel(a, b) }
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Decoded<N, ES, Int> {
  pub unsafe fn bench_encode_regular(self) -> Posit<N, ES, Int> {
    unsafe { self.encode_regular() }
  }

  pub unsafe fn bench_encode_regular_round(self, sticky: Int) -> Posit<N, ES, Int> {
    unsafe { self.encode_regular_round(sticky) }
  }
}

// Export these for inspection with cargo asm

#[unsafe(no_mangle)]
pub fn decode_8(arg: Posit<8, 2, i8>) -> Decoded<8, 2, i8> {
  unsafe { arg.decode_regular() }
}

#[unsafe(no_mangle)]
pub fn decode_16(arg: Posit<16, 2, i16>) -> Decoded<16, 2, i16> {
  unsafe { arg.decode_regular() }
}

#[unsafe(no_mangle)]
pub fn decode_32(arg: Posit<32, 2, i32>) -> Decoded<32, 2, i32> {
  unsafe { arg.decode_regular() }
}

#[unsafe(no_mangle)]
pub fn decode_64(arg: Posit<64, 2, i64>) -> Decoded<64, 2, i64> {
  unsafe { arg.decode_regular() }
}

#[unsafe(no_mangle)]
pub fn encode_8(arg: Decoded<8, 2, i8>, sticky: i8) -> Posit<8, 2, i8> {
  unsafe { arg.encode_regular_round(sticky) }
}

#[unsafe(no_mangle)]
pub fn encode_16(arg: Decoded<16, 2, i16>, sticky: i16) -> Posit<16, 2, i16> {
  unsafe { arg.encode_regular_round(sticky) }
}

#[unsafe(no_mangle)]
pub fn encode_32(arg: Decoded<32, 2, i32>, sticky: i32) -> Posit<32, 2, i32> {
  unsafe { arg.encode_regular_round(sticky) }
}

#[unsafe(no_mangle)]
pub fn encode_64(arg: Decoded<64, 2, i64>, sticky: i64) -> Posit<64, 2, i64> {
  unsafe { arg.encode_regular_round(sticky) }
}

#[unsafe(no_mangle)]
pub fn add_kernel_8(x: Decoded<8, 2, i8>, y: Decoded<8, 2, i8>) -> (Decoded<8, 2, i8>, i8) {
  unsafe { Posit::<8, 2, i8>::add_kernel(x, y) }
}

#[unsafe(no_mangle)]
pub fn add_kernel_16(x: Decoded<16, 2, i16>, y: Decoded<16, 2, i16>) -> (Decoded<16, 2, i16>, i16) {
  unsafe { Posit::<16, 2, i16>::add_kernel(x, y) }
}

#[unsafe(no_mangle)]
pub fn add_kernel_32(x: Decoded<32, 2, i32>, y: Decoded<32, 2, i32>) -> (Decoded<32, 2, i32>, i32) {
  unsafe { Posit::<32, 2, i32>::add_kernel(x, y) }
}

#[unsafe(no_mangle)]
pub fn add_kernel_64(x: Decoded<64, 2, i64>, y: Decoded<64, 2, i64>) -> (Decoded<64, 2, i64>, i64) {
  unsafe { Posit::<64, 2, i64>::add_kernel(x, y) }
}

#[unsafe(no_mangle)]
pub fn add_8(x: Posit<8, 2, i8>, y: Posit<8, 2, i8>) -> Posit<8, 2, i8> {
  x.add(y)
}

#[unsafe(no_mangle)]
pub fn add_16(x: Posit<16, 2, i16>, y: Posit<16, 2, i16>) -> Posit<16, 2, i16> {
  x.add(y)
}

#[unsafe(no_mangle)]
pub fn add_32(x: Posit<32, 2, i32>, y: Posit<32, 2, i32>) -> Posit<32, 2, i32> {
  x.add(y)
}

#[unsafe(no_mangle)]
pub fn add_64(x: Posit<64, 2, i64>, y: Posit<64, 2, i64>) -> Posit<64, 2, i64> {
  x.add(y)
}

#[unsafe(no_mangle)]
pub fn sub_8(x: Posit<8, 2, i8>, y: Posit<8, 2, i8>) -> Posit<8, 2, i8> {
  x.sub(y)
}

#[unsafe(no_mangle)]
pub fn sub_16(x: Posit<16, 2, i16>, y: Posit<16, 2, i16>) -> Posit<16, 2, i16> {
  x.sub(y)
}

#[unsafe(no_mangle)]
pub fn sub_32(x: Posit<32, 2, i32>, y: Posit<32, 2, i32>) -> Posit<32, 2, i32> {
  x.sub(y)
}

#[unsafe(no_mangle)]
pub fn sub_64(x: Posit<64, 2, i64>, y: Posit<64, 2, i64>) -> Posit<64, 2, i64> {
  x.sub(y)
}

#[unsafe(no_mangle)]
pub fn mul_kernel_8(x: Decoded<8, 2, i8>, y: Decoded<8, 2, i8>) -> (Decoded<8, 2, i8>, i8) {
  unsafe { Posit::<8, 2, i8>::mul_kernel(x, y) }
}

#[unsafe(no_mangle)]
pub fn mul_kernel_16(x: Decoded<16, 2, i16>, y: Decoded<16, 2, i16>) -> (Decoded<16, 2, i16>, i16) {
  unsafe { Posit::<16, 2, i16>::mul_kernel(x, y) }
}

#[unsafe(no_mangle)]
pub fn mul_kernel_32(x: Decoded<32, 2, i32>, y: Decoded<32, 2, i32>) -> (Decoded<32, 2, i32>, i32) {
  unsafe { Posit::<32, 2, i32>::mul_kernel(x, y) }
}

#[unsafe(no_mangle)]
pub fn mul_kernel_64(x: Decoded<64, 2, i64>, y: Decoded<64, 2, i64>) -> (Decoded<64, 2, i64>, i64) {
  unsafe { Posit::<64, 2, i64>::mul_kernel(x, y) }
}

#[unsafe(no_mangle)]
pub fn mul_8(x: Posit<8, 2, i8>, y: Posit<8, 2, i8>) -> Posit<8, 2, i8> {
  x.mul(y)
}

#[unsafe(no_mangle)]
pub fn mul_16(x: Posit<16, 2, i16>, y: Posit<16, 2, i16>) -> Posit<16, 2, i16> {
  x.mul(y)
}

#[unsafe(no_mangle)]
pub fn mul_32(x: Posit<32, 2, i32>, y: Posit<32, 2, i32>) -> Posit<32, 2, i32> {
  x.mul(y)
}

#[unsafe(no_mangle)]
pub fn mul_64(x: Posit<64, 2, i64>, y: Posit<64, 2, i64>) -> Posit<64, 2, i64> {
  x.mul(y)
}

#[unsafe(no_mangle)]
pub fn div_kernel_8(x: Decoded<8, 2, i8>, y: Decoded<8, 2, i8>) -> (Decoded<8, 2, i8>, i8) {
  unsafe { Posit::<8, 2, i8>::div_kernel(x, y) }
}

#[unsafe(no_mangle)]
pub fn div_kernel_16(x: Decoded<16, 2, i16>, y: Decoded<16, 2, i16>) -> (Decoded<16, 2, i16>, i16) {
  unsafe { Posit::<16, 2, i16>::div_kernel(x, y) }
}

#[unsafe(no_mangle)]
pub fn div_kernel_32(x: Decoded<32, 2, i32>, y: Decoded<32, 2, i32>) -> (Decoded<32, 2, i32>, i32) {
  unsafe { Posit::<32, 2, i32>::div_kernel(x, y) }
}

#[unsafe(no_mangle)]
pub fn div_kernel_64(x: Decoded<64, 2, i64>, y: Decoded<64, 2, i64>) -> (Decoded<64, 2, i64>, i64) {
  unsafe { Posit::<64, 2, i64>::div_kernel(x, y) }
}

#[unsafe(no_mangle)]
pub fn div_8(x: Posit<8, 2, i8>, y: Posit<8, 2, i8>) -> Posit<8, 2, i8> {
  x.div(y)
}

#[unsafe(no_mangle)]
pub fn div_16(x: Posit<16, 2, i16>, y: Posit<16, 2, i16>) -> Posit<16, 2, i16> {
  x.div(y)
}

#[unsafe(no_mangle)]
pub fn div_32(x: Posit<32, 2, i32>, y: Posit<32, 2, i32>) -> Posit<32, 2, i32> {
  x.div(y)
}

#[unsafe(no_mangle)]
pub fn div_64(x: Posit<64, 2, i64>, y: Posit<64, 2, i64>) -> Posit<64, 2, i64> {
  x.div(y)
}
