use super::*;

/// Implementation of almost all functions, a couple nasty ones need handwritten impls!
macro_rules! impl_common {
  ($int:ty, $uint:ty, $nonzero:ident) => {
    type Unsigned = $uint;

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
      // SAFETY: `self as u8 & 1` can only be 0 or 1
      unsafe { core::mem::transmute::<u8, bool>(self as u8 & 1) }
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
  }
}

impl Int for i128 {}
impl Sealed for i128 {
  impl_common!{i128, u128, NonZeroI128}

  fn overflowing_add_shift(self, rhs: Self) -> (Self, bool) {
    let (mut result, carry) = self.overflowing_add(rhs);
    result >>= u32::from(carry);
    result ^= Self::from(carry) << (Self::BITS - 1);
    (result, carry)
  }
}

impl Int for i64 {}
impl Sealed for i64 {
  impl_common!{i64, u64, NonZeroI64}

  fn overflowing_add_shift(self, rhs: Self) -> (Self, bool) {
    let (mut result, carry) = self.overflowing_add(rhs);
    result >>= u32::from(carry);
    result ^= Self::from(carry) << (Self::BITS - 1);
    (result, carry)
  }
}

impl Int for i32 {}
impl Sealed for i32 {
  impl_common!{i32, u32, NonZeroI32}

  fn overflowing_add_shift(self, rhs: Self) -> (Self, bool) {
    let (mut result, carry) = self.overflowing_add(rhs);
    result >>= u32::from(carry);
    result ^= Self::from(carry) << (Self::BITS - 1);
    (result, carry)
  }
}

impl Int for i16 {}
impl Sealed for i16 {
  impl_common!{i16, u16, NonZeroI16}

  fn overflowing_add_shift(self, rhs: Self) -> (Self, bool) {
    let (mut result, carry) = self.overflowing_add(rhs);
    result >>= u32::from(carry);
    result ^= Self::from(carry) << (Self::BITS - 1);
    (result, carry)
  }
}

impl Int for i8 {}
impl Sealed for i8 {
  impl_common!{i8, u8, NonZeroI8}

  fn overflowing_add_shift(self, rhs: Self) -> (Self, bool) {
    let (mut result, carry) = self.overflowing_add(rhs);
    result >>= u32::from(carry);
    result ^= Self::from(carry) << (Self::BITS - 1);
    (result, carry)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn mask_lsb() {
    assert_eq!(0b01111110_i8.mask_lsb(3), 0b00000110_i8);
    assert_eq!((0xabcd_u16 as i16).mask_lsb(4), 0x000d_u16 as i16);
    assert_eq!((0xabcdabcd_u32 as i32).mask_lsb(4), 0x0000000d_u32 as i32);
    assert_eq!((0xdeadbeefdeadbeef_u64 as i64).mask_lsb(6), 0x2f_i64);
  }

  #[test]
  fn mask_msb() {
    assert_eq!(0b01111110_i8.mask_msb(3), 0b01100000_i8);
    assert_eq!((0xabcd_u16 as i16).mask_msb(4), 0xa000_u16 as i16);
    assert_eq!((0xabcdabcd_u32 as i32).mask_msb(4), 0xa0000000_u32 as i32);
    assert_eq!((0xdeadbeefdeadbeef_u64 as i64).mask_msb(12), 0xdea_i64 << 52);
  }

  #[test]
  fn leading_run_minus_one_zeroes() {
    unsafe {
      assert_eq!((0b00010101u8 as i8 as i8).leading_run_minus_one(), 2);
      assert_eq!((0b00010101u8 as i8 as i16).leading_run_minus_one(), 8 + 2);
      assert_eq!((0b00010101u8 as i8 as i32).leading_run_minus_one(), 24 + 2);
      assert_eq!((0b00010101u8 as i8 as i64).leading_run_minus_one(), 56 + 2);
    }
  }

  #[test]
  fn leading_run_minus_one_ones() {
    unsafe {
      assert_eq!((0b11111000u8 as i8 as i8).leading_run_minus_one(), 4);
      assert_eq!((0b11111000u8 as i8 as i16).leading_run_minus_one(), 8 + 4);
      assert_eq!((0b11111000u8 as i8 as i32).leading_run_minus_one(), 24 + 4);
      assert_eq!((0b11111000u8 as i8 as i64).leading_run_minus_one(), 56 + 4);
    }
  }

  #[test]
  fn not_if_negative() {
    assert_eq!((0b01110110u8 as i8 as i8).not_if_negative(1),  0b01110110u8 as i8 as i8);
    assert_eq!((0b01110110u8 as i8 as i8).not_if_negative(-1), 0b10001001u8 as i8 as i8);
    assert_eq!((0b01110110u8 as i8 as i16).not_if_negative(1),  0b01110110u8 as i8 as i16);
    assert_eq!((0b01110110u8 as i8 as i16).not_if_negative(-1), 0b10001001u8 as i8 as i16);
    assert_eq!((0b01110110u8 as i8 as i32).not_if_negative(1),  0b01110110u8 as i8 as i32);
    assert_eq!((0b01110110u8 as i8 as i32).not_if_negative(-1), 0b10001001u8 as i8 as i32);
    assert_eq!((0b01110110u8 as i8 as i64).not_if_negative(1),  0b01110110u8 as i8 as i64);
    assert_eq!((0b01110110u8 as i8 as i64).not_if_negative(-1), 0b10001001u8 as i8 as i64);
  }

  #[test]
  fn not_if_positive() {
    assert_eq!((0b11100110u8 as i8 as i8).not_if_positive(1),  0b00011001u8 as i8 as i8);
    assert_eq!((0b11100110u8 as i8 as i8).not_if_positive(-1), 0b11100110u8 as i8 as i8);
    assert_eq!((0b11100110u8 as i8 as i16).not_if_positive(1),  0b00011001u8 as i8 as i16);
    assert_eq!((0b11100110u8 as i8 as i16).not_if_positive(-1), 0b11100110u8 as i8 as i16);
    assert_eq!((0b11100110u8 as i8 as i32).not_if_positive(1),  0b00011001u8 as i8 as i32);
    assert_eq!((0b11100110u8 as i8 as i32).not_if_positive(-1), 0b11100110u8 as i8 as i32);
    assert_eq!((0b11100110u8 as i8 as i64).not_if_positive(1),  0b00011001u8 as i8 as i64);
    assert_eq!((0b11100110u8 as i8 as i64).not_if_positive(-1), 0b11100110u8 as i8 as i64);
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
      (0b10_000000u8 as i8).overflowing_add_shift(0b01_011000u8 as i8),
      (0b11_011000u8 as i8, false)
    );
    assert_eq!(
      (0b10_000000u8 as i8).overflowing_add_shift(0b10_011000u8 as i8),
      (0b10_001100u8 as i8, true)
    );
  }
}
