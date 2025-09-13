use super::{Int, Sealed};

/// Implementation of almost all functions, a couple nasty ones need handwritten impls!
macro_rules! impl_common {
  ($int:ty, $uint:ty, $double:ty, $nonzero:ident) => {
    type Unsigned = $uint;
    type Double = $double;

    const ZERO: Self = 0;
    const ONE: Self = 1;
    const MIN: Self = <$int>::MIN;
    const MAX: Self = <$int>::MAX;
    const BITS: u32 = <$int>::BITS;

    #[inline]
    fn as_unsigned(self) -> $uint { self as $uint }

    #[inline]
    fn of_unsigned(x: $uint) -> Self { x as $int }

    #[inline]
    fn as_u32(self) -> u32 {
      debug_assert!(u32::try_from(self).is_ok());
      self as u32
    }

    #[inline]
    fn of_u32(x: u32) -> Self {
      debug_assert!(Self::try_from(x).is_ok());
      x as $int
    }

    #[inline]
    fn is_positive(self) -> bool {
      self >= 0
      // let mask = self >> (Self::BITS - 1);
      // unsafe { core::mem::transmute::<u8, bool>((mask & 1) as u8) }
    }

    #[inline]
    fn abs(self) -> Self {
      self.abs()
    }

    #[inline]
    fn lshr(self, n: u32) -> Self { ((self as $uint) >> n) as $int }

    #[inline]
    fn mask_lsb(self, n: u32) -> Self {
      let mask = (1 as $int << n).wrapping_sub(1);
      self & mask
    }

    #[inline]
    fn mask_msb(self, n: u32) -> Self {
      let mask = (1 as $int << (Self::BITS - n)).wrapping_sub(1);
      self & !mask
    }

    #[inline]
    fn get_lsb(self) -> bool {
      self & 1 == 1
    }

    fn leading_zeros(self) -> u32 {
      const { assert!(Self::BITS < u8::MAX as u32 - 1) }
      self.leading_zeros()
    }

    #[inline]
    unsafe fn leading_zeros_nonzero(self) -> u32 {
      const { assert!(Self::BITS < u8::MAX as u32 - 1) }
      unsafe{core::num::$nonzero::new_unchecked(self)}.leading_zeros()
    }

    unsafe fn leading_run_minus_one(self) -> u32 {
      let y = self ^ (self << 1);
      let z = unsafe { core::num::$nonzero::new_unchecked(y) };
      z.leading_zeros()
    }

    #[inline]
    fn not_if_positive(self, control: Self) -> Self {
      // !self.not_if_negative(control)
      // Slightly more ILP
      let mask = control >> (Self::BITS - 1);
      !self ^ mask
    }

    #[inline]
    fn not_if_negative(self, control: Self) -> Self {
      let mask = control >> (Self::BITS - 1);
      self ^ mask
    }

    #[inline]
    fn wrapping_add(self, other: Self) -> Self { self.wrapping_add(other) }

    #[inline]
    fn wrapping_sub(self, other: Self) -> Self { self.wrapping_sub(other) }

    #[inline]
    fn wrapping_neg(self) -> Self { self.wrapping_neg() }

    #[inline]
    fn overflowing_add(self, other: Self) -> (Self, bool) { self.overflowing_add(other) }

    fn multiword_shl(self, n: u32) -> (Self, Self, usize) {
      // Codegen seems pretty great when looking in godbolt!
      let bytes = n / Self::BITS * Self::BITS / 8;
      let bits = n % Self::BITS;
      let lo = self << bits;
      let hi = self >> (Self::BITS - bits);
      (hi, lo, bytes as usize)
    }
  }
}

macro_rules! impl_common_doubling {
  ($int:ty, $double:ty) => {
    #[inline]
    fn doubling_mul(self, other: Self) -> Self::Double {
      self as $double * other as $double
    }

    fn shift_div_rem(self, other: Self, precision: u32) -> (Self, Self) {
      let a = self as $double << precision;
      let b = other as $double;
      let mut div = a / b;
      let rem = a % b;
      // PDP/C/Rust division rounds towards 0, not towards -∞. For positive numbers this is the
      // same. For negative numbers, we need to subtract 1 if the division is inexact.
      div -= ((div < 0) & (rem != 0)) as $double;
      (div as $int, rem as $int)
    }    
  }
}

impl Int for i128 {}
impl Sealed for i128 {
  impl_common!{i128, u128, super::double::Pair<i128>, NonZeroI128}

  fn doubling_mul(self, other: Self) -> Self::Double {
    todo!()
  }

  fn shift_div_rem(self, other: Self, precision: u32) -> (Self, Self) {
    todo!()
  }

  fn overflowing_add_shift(self, rhs: Self) -> (Self, bool) {
    let (mut result, carry) = self.overflowing_add(rhs);
    result >>= u32::from(carry);
    result ^= Self::from(carry) << (Self::BITS - 1);
    (result, carry)
  }
}

impl Int for i64 {}
impl Sealed for i64 {
  impl_common!{i64, u64, i128, NonZeroI64}
  impl_common_doubling!{i64, i128}

  fn overflowing_add_shift(self, rhs: Self) -> (Self, bool) {
    let (mut result, carry) = self.overflowing_add(rhs);
    result >>= u32::from(carry);
    result ^= Self::from(carry) << (Self::BITS - 1);
    (result, carry)
  }
}

impl Int for i32 {}
impl Sealed for i32 {
  impl_common!{i32, u32, i64, NonZeroI32}
  impl_common_doubling!{i32, i64}

  fn overflowing_add_shift(self, rhs: Self) -> (Self, bool) {
    let (mut result, carry) = self.overflowing_add(rhs);
    result >>= u32::from(carry);
    result ^= Self::from(carry) << (Self::BITS - 1);
    (result, carry)
  }
}

impl Int for i16 {}
impl Sealed for i16 {
  impl_common!{i16, u16, i32, NonZeroI16}
  impl_common_doubling!{i16, i32}

  fn overflowing_add_shift(self, rhs: Self) -> (Self, bool) {
    let (mut result, carry) = self.overflowing_add(rhs);
    result >>= u32::from(carry);
    result ^= Self::from(carry) << (Self::BITS - 1);
    (result, carry)
  }
}

impl Int for i8 {}
impl Sealed for i8 {
  impl_common!{i8, u8, i16, NonZeroI8}
  impl_common_doubling!{i8, i16}

  fn overflowing_add_shift(self, rhs: Self) -> (Self, bool) {
    let (mut result, carry) = self.overflowing_add(rhs);
    result >>= u32::from(carry);
    result ^= Self::from(carry) << (Self::BITS - 1);
    (result, carry)
  }
}

#[cfg(test)]
#[allow(overflowing_literals)]
mod tests {
  use super::*;

  #[test]
  fn mask_lsb() {
    assert_eq!(0b01111110_i8.mask_lsb(3), 0b00000110_i8);
    assert_eq!(0xabcd_i16.mask_lsb(4), 0x000d_i16);
    assert_eq!(0xabcdabcd_i32.mask_lsb(4), 0x0000000d_i32);
    assert_eq!(0xdeadbeefdeadbeef_i64.mask_lsb(6), 0x2f_i64);
  }

  #[test]
  fn mask_msb() {
    assert_eq!(0b01111110_i8.mask_msb(3), 0b01100000_i8);
    assert_eq!(0xabcd_i16.mask_msb(4), 0xa000_i16);
    assert_eq!(0xabcdabcd_i32.mask_msb(4), 0xa0000000_i32);
    assert_eq!(0xdeadbeefdeadbeef_i64.mask_msb(12), 0xdea_i64 << 52);
  }

  #[test]
  fn leading_run_minus_one_zeroes() {
    unsafe {
      assert_eq!((0b00010101i8 as i8).leading_run_minus_one(), 2);
      assert_eq!((0b00010101i8 as i16).leading_run_minus_one(), 8 + 2);
      assert_eq!((0b00010101i8 as i32).leading_run_minus_one(), 24 + 2);
      assert_eq!((0b00010101i8 as i64).leading_run_minus_one(), 56 + 2);
    }
  }

  #[test]
  fn leading_run_minus_one_ones() {
    unsafe {
      assert_eq!((0b11111000i8 as i8).leading_run_minus_one(), 4);
      assert_eq!((0b11111000i8 as i16).leading_run_minus_one(), 8 + 4);
      assert_eq!((0b11111000i8 as i32).leading_run_minus_one(), 24 + 4);
      assert_eq!((0b11111000i8 as i64).leading_run_minus_one(), 56 + 4);
    }
  }

  #[test]
  fn not_if_negative() {
    assert_eq!((0b01110110i8 as i8).not_if_negative(1),  0b01110110i8 as i8);
    assert_eq!((0b01110110i8 as i8).not_if_negative(-1), 0b10001001i8 as i8);
    assert_eq!((0b01110110i8 as i16).not_if_negative(1),  0b01110110i8 as i16);
    assert_eq!((0b01110110i8 as i16).not_if_negative(-1), 0b10001001i8 as i16);
    assert_eq!((0b01110110i8 as i32).not_if_negative(1),  0b01110110i8 as i32);
    assert_eq!((0b01110110i8 as i32).not_if_negative(-1), 0b10001001i8 as i32);
    assert_eq!((0b01110110i8 as i64).not_if_negative(1),  0b01110110i8 as i64);
    assert_eq!((0b01110110i8 as i64).not_if_negative(-1), 0b10001001i8 as i64);
  }

  #[test]
  fn not_if_positive() {
    assert_eq!((0b11100110i8 as i8).not_if_positive(1),  0b00011001i8 as i8);
    assert_eq!((0b11100110i8 as i8).not_if_positive(-1), 0b11100110i8 as i8);
    assert_eq!((0b11100110i8 as i16).not_if_positive(1),  0b00011001i8 as i16);
    assert_eq!((0b11100110i8 as i16).not_if_positive(-1), 0b11100110i8 as i16);
    assert_eq!((0b11100110i8 as i32).not_if_positive(1),  0b00011001i8 as i32);
    assert_eq!((0b11100110i8 as i32).not_if_positive(-1), 0b11100110i8 as i32);
    assert_eq!((0b11100110i8 as i64).not_if_positive(1),  0b00011001i8 as i64);
    assert_eq!((0b11100110i8 as i64).not_if_positive(-1), 0b11100110i8 as i64);
  }

  #[test]
  fn overflowing_add_shift() {
    assert_eq!(
      (0b01_000000i8).overflowing_add_shift(0b00_100000i8),
      (0b01_100000i8, false)
    );
    assert_eq!(
      (0b01_000000i8).overflowing_add_shift(0b01_000000i8),
      (0b01_000000i8, true)
    );
    assert_eq!(
      (0b10_000000i8).overflowing_add_shift(0b01_011000i8),
      (0b11_011000i8, false)
    );
    assert_eq!(
      (0b10_000000i8).overflowing_add_shift(0b10_011000i8),
      (0b10_001100i8, true)
    );
  }

  #[test]
  fn multiword_shl_small() {
    assert_eq!(
      (0x1234abcd_i32).multiword_shl(4),
      (0x00000001, 0x234abcd0, 0),
    );
    assert_eq!(
      (0xa234abcd_i32).multiword_shl(4),
      (0xfffffffa, 0x234abcd0, 0),
    );
  }

  #[test]
  fn multiword_shl_exact() {
    assert_eq!(
      (0x1234abcd_i32).multiword_shl(32 + 4),
      (0x00000001, 0x234abcd0, 4),
    );
    assert_eq!(
      (0xa234abcd_i32).multiword_shl(32 + 4),
      (0xfffffffa, 0x234abcd0, 4),
    );

    assert_eq!(
      (0x1234abcd_i32).multiword_shl(64 + 4),
      (0x00000001, 0x234abcd0, 8),
    );
    assert_eq!(
      (0xa234abcd_i32).multiword_shl(64 + 4),
      (0xfffffffa, 0x234abcd0, 8),
    );
  }

  #[test]
  fn multiword_shl_inexact() {
    assert_eq!(
      (0x1234abcd_i32).multiword_shl(16 + 4),
      (0x0001234a, 0xbcd00000, 0),
    );
    assert_eq!(
      (0xa234abcd_i32).multiword_shl(16 + 4),
      (0xfffa234a, 0xbcd00000, 0),
    );

    assert_eq!(
      (0x1234abcd_i32).multiword_shl(48 + 4),
      (0x0001234a, 0xbcd00000, 4),
    );
    assert_eq!(
      (0xa234abcd_i32).multiword_shl(48 + 4),
      (0xfffa234a, 0xbcd00000, 4),
    );
  }
}
