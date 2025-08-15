//! This module contains all the implementations of the necessary underlying integer operations
//! needed for the software implementation of posit arithmetic. These are hidden from the
//! end-user, which only sees the sealed [`Int`] trait, implemented for `i8`, `i16`, `i32`, `i64`,
//! and `i128`.

/// The trait for the underlying machine integer types that can be used to represent a posit
/// (only satisfied by `i8`, `i16`, `i32`, `i64`, and `i128`).
///
/// This is a *sealed* type.
pub trait Int: Sealed {}

/// Actual operations implemented here.
pub trait Sealed:
  Copy + Clone +
  Eq + Ord +
  core::fmt::Debug + core::fmt::Display + core::fmt::Binary +
  core::ops::Add<Self, Output=Self> + core::ops::AddAssign<Self> +
  core::ops::Sub<Self, Output=Self> + core::ops::AddAssign<Self> +
  // core::ops::Mul<Self, Output=Self> +
  // core::ops::Div<Self, Output=Self> +
  core::ops::Shl<u32, Output=Self> +
  core::ops::Shr<u32, Output=Self> +
  core::ops::BitAnd<Output=Self> +
  core::ops::BitOr<Output=Self> + core::ops::BitOrAssign +
  core::ops::BitXor<Output=Self> +
  core::ops::Not<Output=Self> +
  core::ops::Neg<Output=Self> +
  From<bool> + Into<i128>
{
  type Unsigned;

  const ZERO: Self;
  const ONE: Self;
  const MIN: Self;
  const MAX: Self;
  const BITS: u32;

  fn as_unsigned(self) -> Self::Unsigned;
  fn of_unsigned(x: Self::Unsigned) -> Self;

  fn as_u32(self) -> u32;
  fn of_u32(x: u32) -> Self;

  fn is_positive(self) -> bool;
  fn abs(self) -> Self;

  /// Logical shift right (rather than arithmetic shift). Short for `(self as uX >> n) as iX`.
  fn lshr(self, n: u32) -> Self;

  /// Set all bits more significant than `n` to 0.
  ///
  /// ```ignore
  /// assert_eq!(0xabcd_i16.mask_lsb(4), 0x000d_i16)
  /// ```
  fn mask_lsb(self, n: u32) -> Self;

  /// Set all bits less significant than `BITS - n` to 0.
  ///
  /// ```ignore
  /// assert_eq!(0xabcd_i16.mask_msb(4), 0xa000_i16)
  /// ```
  fn mask_msb(self, n: u32) -> Self;

  /// Get the lsb of `self` as a bool
  fn get_lsb(self) -> bool;

  /// Number of leading (most significant) 0 bits until the first 1.
  fn leading_zeros(self) -> u32;

  /// As [Sealed::leading_zeros], but is undefined if `self` is zero.
  unsafe fn leading_zeros_nonzero(self) -> u32;

  /// Number of leading (most significant) 0 bits until the first 1 OR number of leading 1 bits
  /// until the first 0, *minus 1*.
  ///
  /// If `self` is `Int::ZERO` or `Int::MIN`, calling this function is *undefined behaviour*.
  ///
  /// ```ignore
  /// # use crate::underlying::Sealed;
  /// assert_eq!((0b00010101u8 as i8).leading_run_minus_one(), 2);
  /// assert_eq!((0b11111000u8 as i8).leading_run_minus_one(), 4);
  /// ```
  unsafe fn leading_run_minus_one(self) -> u32;

  /// Short for `if control < 0 { self } else { !self }`.
  fn not_if_negative(self, control: Self) -> Self;

  /// Short for `if control >= 0 { !self } else { self }`.
  fn not_if_positive(self, control: Self) -> Self;

  fn wrapping_add(self, other: Self) -> Self;
  fn wrapping_sub(self, other: Self) -> Self;
  fn wrapping_neg(self) -> Self;

  fn overflowing_add(self, other: Self) -> (Self, bool);

  /// If `self + other` doesn't overflow, return `(self + other, false)`. If it does overflow,
  /// return `(self.midpoint(other), true)` (i.e. `(self + other) / 2` as if it were evaluated in
  /// a sufficiently large type).
  fn overflowing_add_shift(self, other: Self) -> (Self, bool);
}

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

/// One line of the [`const_as`] function.
macro_rules! const_as_line {
  ($x:ident, $t:ty, $u:ty) => {
    if const { T::BITS == <$t>::BITS && U::BITS == <$u>::BITS } {
      // SAFETY: Because T, U, $t, $u, are guaranteed to be `iX`, then `$t` is `T` and `$u` is `U`;
      // therefore both transmute_copy are no-ops.
      let t = unsafe { ::core::mem::transmute_copy::<T, $t>(&$x) };
      let u = t as $u;
      return unsafe { ::core::mem::transmute_copy::<$u, U>(&u) }
    }
  }
}

/// A type-generic and `const` version of the keyword `as`, for casting between [`Int`]s.
///
/// ```ignore
/// # use fast_posit::underlying::const_as;
/// assert_eq!(const_as::<i16, i32>(1234i16), 1234i16 as i32);
/// assert_eq!(const_as::<i128, i64>(-16i128), -126i128 as i64);
/// ```
pub const fn const_as<T: Int, U: Int>(x: T) -> U {
  const_as_line!(x, i8, i8);
  const_as_line!(x, i8, i16);
  const_as_line!(x, i8, i32);
  const_as_line!(x, i8, i64);
  const_as_line!(x, i8, i128);
  const_as_line!(x, i16, i8);
  const_as_line!(x, i16, i16);
  const_as_line!(x, i16, i32);
  const_as_line!(x, i16, i64);
  const_as_line!(x, i16, i128);
  const_as_line!(x, i32, i8);
  const_as_line!(x, i32, i16);
  const_as_line!(x, i32, i32);
  const_as_line!(x, i32, i64);
  const_as_line!(x, i32, i128);
  const_as_line!(x, i64, i8);
  const_as_line!(x, i64, i16);
  const_as_line!(x, i64, i32);
  const_as_line!(x, i64, i64);
  const_as_line!(x, i64, i128);
  const_as_line!(x, i128, i8);
  const_as_line!(x, i128, i16);
  const_as_line!(x, i128, i32);
  const_as_line!(x, i128, i64);
  const_as_line!(x, i128, i128);
  unreachable!() // cannot be const { unreachable!() }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn const_as_1() {
    const VALUE: i32 = const_as(1i128);
    assert_eq!(VALUE, 1i32);
  }

  #[test]
  fn const_as_2() {
    const VALUE: i32 = const_as(-1i128);
    assert_eq!(VALUE, -1i32);
  }

  #[test]
  fn const_as_3() {
    const VALUE: i32 = const_as(0i128);
    assert_eq!(VALUE, 0i32);
  }

  #[test]
  fn const_as_4() {
    const VALUE: i32 = const_as(0xdeadbeefi128);
    assert_eq!(VALUE, 0xdeadbeefu32 as i32);
  }

  #[test]
  fn const_as_5() {
    const VALUE: i32 = const_as(0x71u8 as i8);
    assert_eq!(VALUE, 0x00000071u32 as i32);
  }

  #[test]
  fn const_as_6() {
    const VALUE: i32 = const_as(0xf1u8 as i8);
    assert_eq!(VALUE, 0xfffffff1u32 as i32);
  }

  #[test]
  fn const_as_7() {
    const VALUE: i16 = const_as(0x1337i16);
    assert_eq!(VALUE, 0x1337i16);
  }

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
