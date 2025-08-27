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

mod int;
mod const_as;
pub use const_as::const_as;
