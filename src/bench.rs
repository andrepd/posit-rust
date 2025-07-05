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
}

// Export these for inspection with cargo asm

#[unsafe(no_mangle)]
#[inline]
pub fn decode_8(arg: Posit<8, 2, i8>) -> Decoded<8, 2, i8> {
  unsafe { arg.decode_regular() }
}

#[unsafe(no_mangle)]
#[inline]
pub fn decode_16(arg: Posit<16, 2, i16>) -> Decoded<16, 2, i16> {
  unsafe { arg.decode_regular() }
}

#[unsafe(no_mangle)]
#[inline]
pub fn decode_32(arg: Posit<32, 2, i32>) -> Decoded<32, 2, i32> {
  unsafe { arg.decode_regular() }
}

#[unsafe(no_mangle)]
#[inline]
pub fn decode_64(arg: Posit<64, 2, i64>) -> Decoded<64, 2, i64> {
  unsafe { arg.decode_regular() }
}
