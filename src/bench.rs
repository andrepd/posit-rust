//! Re-export some internals for benchmarking purposes; available with feature = "bench".

use crate::posit::{Posit, Decoded};
use crate::{RoundFrom, RoundInto};

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

  pub unsafe fn bench_sqrt_kernel(a: Decoded<N, ES, Int>) -> (Decoded<N, ES, Int>, Int) {
    unsafe { Self::sqrt_kernel(a) }
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

// Export these for inspection with `cargo asm`.

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

//

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

//

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
  x + y
}

#[unsafe(no_mangle)]
pub fn add_16(x: Posit<16, 2, i16>, y: Posit<16, 2, i16>) -> Posit<16, 2, i16> {
  x + y
}

#[unsafe(no_mangle)]
pub fn add_32(x: Posit<32, 2, i32>, y: Posit<32, 2, i32>) -> Posit<32, 2, i32> {
  x + y
}

#[unsafe(no_mangle)]
pub fn add_64(x: Posit<64, 2, i64>, y: Posit<64, 2, i64>) -> Posit<64, 2, i64> {
  x + y
}

#[unsafe(no_mangle)]
pub fn sub_8(x: Posit<8, 2, i8>, y: Posit<8, 2, i8>) -> Posit<8, 2, i8> {
  x - y
}

#[unsafe(no_mangle)]
pub fn sub_16(x: Posit<16, 2, i16>, y: Posit<16, 2, i16>) -> Posit<16, 2, i16> {
  x - y
}

#[unsafe(no_mangle)]
pub fn sub_32(x: Posit<32, 2, i32>, y: Posit<32, 2, i32>) -> Posit<32, 2, i32> {
  x - y
}

#[unsafe(no_mangle)]
pub fn sub_64(x: Posit<64, 2, i64>, y: Posit<64, 2, i64>) -> Posit<64, 2, i64> {
  x - y
}

//

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
  x * y
}

#[unsafe(no_mangle)]
pub fn mul_16(x: Posit<16, 2, i16>, y: Posit<16, 2, i16>) -> Posit<16, 2, i16> {
  x * y
}

#[unsafe(no_mangle)]
pub fn mul_32(x: Posit<32, 2, i32>, y: Posit<32, 2, i32>) -> Posit<32, 2, i32> {
  x * y
}

#[unsafe(no_mangle)]
pub fn mul_64(x: Posit<64, 2, i64>, y: Posit<64, 2, i64>) -> Posit<64, 2, i64> {
  x * y
}

//

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
  x / y
}

#[unsafe(no_mangle)]
pub fn div_16(x: Posit<16, 2, i16>, y: Posit<16, 2, i16>) -> Posit<16, 2, i16> {
  x / y
}

#[unsafe(no_mangle)]
pub fn div_32(x: Posit<32, 2, i32>, y: Posit<32, 2, i32>) -> Posit<32, 2, i32> {
  x / y
}

#[unsafe(no_mangle)]
pub fn div_64(x: Posit<64, 2, i64>, y: Posit<64, 2, i64>) -> Posit<64, 2, i64> {
  x / y
}

//

#[unsafe(no_mangle)]
pub fn sqrt_kernel_8(x: Decoded<8, 2, i8>) -> (Decoded<8, 2, i8>, i8) {
  unsafe { Posit::<8, 2, i8>::sqrt_kernel(x) }
}

#[unsafe(no_mangle)]
pub fn sqrt_kernel_16(x: Decoded<16, 2, i16>) -> (Decoded<16, 2, i16>, i16) {
  unsafe { Posit::<16, 2, i16>::sqrt_kernel(x) }
}

#[unsafe(no_mangle)]
pub fn sqrt_kernel_32(x: Decoded<32, 2, i32>) -> (Decoded<32, 2, i32>, i32) {
  unsafe { Posit::<32, 2, i32>::sqrt_kernel(x) }
}

#[unsafe(no_mangle)]
pub fn sqrt_kernel_64(x: Decoded<64, 2, i64>) -> (Decoded<64, 2, i64>, i64) {
  unsafe { Posit::<64, 2, i64>::sqrt_kernel(x) }
}

#[unsafe(no_mangle)]
pub fn sqrt_8(x: Posit<8, 2, i8>) -> Posit<8, 2, i8> {
  x.sqrt()
}

#[unsafe(no_mangle)]
pub fn sqrt_16(x: Posit<16, 2, i16>) -> Posit<16, 2, i16> {
  x.sqrt()
}

#[unsafe(no_mangle)]
pub fn sqrt_32(x: Posit<32, 2, i32>) -> Posit<32, 2, i32> {
  x.sqrt()
}

#[unsafe(no_mangle)]
pub fn sqrt_64(x: Posit<64, 2, i64>) -> Posit<64, 2, i64> {
  x.sqrt()
}

//

#[unsafe(no_mangle)]
pub fn nearest_int_8(x: crate::p8) -> crate::p8 {
  x.nearest_int()
}

#[unsafe(no_mangle)]
pub fn nearest_int_16(x: crate::p16) -> crate::p16 {
  x.nearest_int()
}

#[unsafe(no_mangle)]
pub fn nearest_int_32(x: crate::p32) -> crate::p32 {
  x.nearest_int()
}

#[unsafe(no_mangle)]
pub fn nearest_int_64(x: crate::p64) -> crate::p64 {
  x.nearest_int()
}

#[unsafe(no_mangle)]
pub fn floor_8(x: crate::p8) -> crate::p8 {
  x.floor()
}

#[unsafe(no_mangle)]
pub fn floor_16(x: crate::p16) -> crate::p16 {
  x.floor()
}

#[unsafe(no_mangle)]
pub fn floor_32(x: crate::p32) -> crate::p32 {
  x.floor()
}

#[unsafe(no_mangle)]
pub fn floor_64(x: crate::p64) -> crate::p64 {
  x.floor()
}

#[unsafe(no_mangle)]
pub fn ceil_8(x: crate::p8) -> crate::p8 {
  x.ceil()
}

#[unsafe(no_mangle)]
pub fn ceil_16(x: crate::p16) -> crate::p16 {
  x.ceil()
}

#[unsafe(no_mangle)]
pub fn ceil_32(x: crate::p32) -> crate::p32 {
  x.ceil()
}

#[unsafe(no_mangle)]
pub fn ceil_64(x: crate::p64) -> crate::p64 {
  x.ceil()
}

//

#[unsafe(no_mangle)]
pub fn quire_add_8(quire: &mut crate::q8, posit: crate::p8) {
  *quire += posit
}

#[unsafe(no_mangle)]
pub fn quire_add_16(quire: &mut crate::q16, posit: crate::p16) {
  *quire += posit
}

#[unsafe(no_mangle)]
pub fn quire_add_32(quire: &mut crate::q32, posit: crate::p32) {
  *quire += posit
}

#[unsafe(no_mangle)]
pub fn quire_add_64(quire: &mut crate::q64, posit: crate::p64) {
  *quire += posit
}

#[unsafe(no_mangle)]
pub fn quire_add_kernel_8(quire: &mut crate::q8, decoded: Decoded<8, 2, i8>) {
  unsafe { quire.add_posit_kernel(decoded) }
}

#[unsafe(no_mangle)]
pub fn quire_add_kernel_16(quire: &mut crate::q16, decoded: Decoded<16, 2, i8>) {
  unsafe { quire.add_posit_kernel(decoded) }
}

#[unsafe(no_mangle)]
pub fn quire_add_kernel_32(quire: &mut crate::q32, decoded: Decoded<32, 2, i8>) {
  unsafe { quire.add_posit_kernel(decoded) }
}

#[unsafe(no_mangle)]
pub fn quire_add_kernel_64(quire: &mut crate::q64, decoded: Decoded<64, 2, i8>) {
  unsafe { quire.add_posit_kernel(decoded) }
}

#[unsafe(no_mangle)]
pub fn quire_add_prod_8(quire: &mut crate::q8, a: crate::p8, b: crate::p8) {
  quire.add_prod(a, b)
}

#[unsafe(no_mangle)]
pub fn quire_add_prod_16(quire: &mut crate::q16, a: crate::p16, b: crate::p16) {
  quire.add_prod(a, b)
}

#[unsafe(no_mangle)]
pub fn quire_add_prod_32(quire: &mut crate::q32, a: crate::p32, b: crate::p32) {
  quire.add_prod(a, b)
}

#[unsafe(no_mangle)]
pub fn quire_add_prod_64(quire: &mut crate::q64, a: crate::p64, b: crate::p64) {
  quire.add_prod(a, b)
}

#[unsafe(no_mangle)]
pub fn quire_add_prod_kernel_8(quire: &mut crate::q8, a: Decoded<8, 2, i8>, b: Decoded<8, 2, i8>) {
  unsafe { quire.add_posit_prod_kernel(a, b) }
}

#[unsafe(no_mangle)]
pub fn quire_add_prod_kernel_16(quire: &mut crate::q16, a: Decoded<16, 2, i16>, b: Decoded<16, 2, i16>) {
  unsafe { quire.add_posit_prod_kernel(a, b) }
}

#[unsafe(no_mangle)]
pub fn quire_add_prod_kernel_32(quire: &mut crate::q32, a: Decoded<32, 2, i32>, b: Decoded<32, 2, i32>) {
  unsafe { quire.add_posit_prod_kernel(a, b) }
}

#[unsafe(no_mangle)]
pub fn quire_add_prod_kernel_64(quire: &mut crate::q64, a: Decoded<64, 2, i64>, b: Decoded<64, 2, i64>) {
  unsafe { quire.add_posit_prod_kernel(a, b) }
}

//

#[unsafe(no_mangle)]
pub fn round_i32_to_p8(num: i32) -> crate::p8 {
  num.round_into()
}

#[unsafe(no_mangle)]
pub fn round_i32_to_p32(num: i32) -> crate::p32 {
  num.round_into()
}

#[unsafe(no_mangle)]
pub fn round_i32_to_p64(num: i32) -> crate::p64 {
  num.round_into()
}

#[unsafe(no_mangle)]
pub fn round_p32_to_i8(num: crate::p32) -> i8 {
  num.round_into()
}

#[unsafe(no_mangle)]
pub fn round_p32_to_i32(num: crate::p32) -> i32 {
  num.round_into()
}

#[unsafe(no_mangle)]
pub fn round_p32_to_i64(num: crate::p32) -> i64 {
  num.round_into()
}

//

#[unsafe(no_mangle)]
pub fn round_f32_to_p8(num: f32) -> crate::p8 {
  num.round_into()
}

#[unsafe(no_mangle)]
pub fn round_f32_to_p32(num: f32) -> crate::p32 {
  num.round_into()
}

#[unsafe(no_mangle)]
pub fn round_f32_to_p64(num: f32) -> crate::p64 {
  num.round_into()
}

//

#[unsafe(no_mangle)]
pub fn round_p8_to_f32(num: crate::p8) -> f32 {
  num.round_into()
}

#[unsafe(no_mangle)]
pub fn round_p32_to_f32(num: crate::p32) -> f32 {
  num.round_into()
}

#[unsafe(no_mangle)]
pub fn round_p64_to_f32(num: crate::p64) -> f32 {
  num.round_into()
}

//

#[unsafe(no_mangle)]
pub fn round_p32_to_p16(num: crate::p32) -> crate::p16 {
  num.convert()
}

#[unsafe(no_mangle)]
pub fn round_p16_to_p32(num: crate::p16) -> crate::p32 {
  num.convert()
}
