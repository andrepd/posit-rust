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
  core::ops::Add<Self, Output=Self> +
  core::ops::Sub<Self, Output=Self> +
  // core::ops::Mul<Self, Output=Self> +
  // core::ops::Div<Self, Output=Self> +
  core::ops::Shl<u32, Output=Self> +
  core::ops::Shr<u32, Output=Self> +
  core::ops::BitAnd<Output=Self> +
  core::ops::BitOr<Output=Self> +
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
  fn mask_lsb(self, n: u32) -> Self;

  /// Number of leading (most significant) 0 bits until the first 1.
  fn leading_zeros(self) -> u32;

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
      let mask = (1 << n) - 1;
      self & mask
    }

    fn leading_zeros(self) -> u32 {
      const { assert!(Self::BITS < u8::MAX as u32 - 1) }
      self.leading_zeros()
    }
  }
}

impl Int for i128 {}
impl Sealed for i128 {
  impl_common!{i128, u128, NonZeroI128}
}

impl Int for i64 {}
impl Sealed for i64 {
  impl_common!{i64, u64, NonZeroI64}
}

impl Int for i32 {}
impl Sealed for i32 {
  impl_common!{i32, u32, NonZeroI32}
}

impl Int for i16 {}
impl Sealed for i16 {
  impl_common!{i16, u16, NonZeroI16}
}

impl Int for i8 {}
impl Sealed for i8 {
  impl_common!{i8, u8, NonZeroI8}
}

/// Hack to cast const values (as `i128`) back to `Int` in const as well.
pub const fn const_i128_as_int<T: Int>(x: i128) -> T {
  // What a roundabout way to do this... Needed because no `const` traits.
  let le_bytes = x.to_le_bytes();
  if cfg!(target_endian = "little") {
    // SAFETY: In a little endian architecture, this is equivalent to `x as T`
    unsafe { core::mem::transmute_copy(&le_bytes) }
  } else {
    unimplemented!()
  }
}
