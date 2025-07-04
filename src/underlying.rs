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
  From<bool>
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

    fn as_unsigned(self) -> $uint { self as $uint }

    fn of_unsigned(x: $uint) -> Self { x as $int }

    fn as_u32(self) -> u32 {
      debug_assert!(u32::try_from(self).is_ok());
      self as u32
    }

    fn of_u32(x: u32) -> Self {
      debug_assert!(Self::try_from(x).is_ok());
      x as $int
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
