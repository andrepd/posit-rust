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
  core::fmt::Debug + core::fmt::Display + core::fmt::Binary +
  Copy + Clone +
  Eq + Ord +
  core::hash::Hash + Default +
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
  type Unsigned: Unsigned;
  type Double: Double<Single = Self>;

  const ZERO: Self;
  const ONE: Self;
  const MIN: Self;
  const MAX: Self;
  const BITS: u32;

  fn as_unsigned(self) -> Self::Unsigned;
  fn of_unsigned(x: Self::Unsigned) -> Self;

  fn as_u32(self) -> u32;
  fn of_u32(x: u32) -> Self;

  fn to_be(self) -> Self;
  fn from_be(self) -> Self;

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
  fn wrapping_abs(self) -> Self;

  fn overflowing_add(self, other: Self) -> (Self, bool);
  fn carrying_add(self, other: Self, carry: bool) -> (Self, bool);

  /// If `self + other` doesn't overflow, return `(self + other, false)`. If it does overflow,
  /// return `(self.midpoint(other), true)` (i.e. `(self + other) / 2` as if it were evaluated in
  /// a sufficiently large type).
  fn overflowing_add_shift(self, other: Self) -> (Self, bool);

  /// Multiply without overflow or loss of precision, by returning a type that's twice as wide as
  /// `Self`.
  fn doubling_mul(self, other: Self) -> Self::Double;

  /// Compute the result of `(self << precision) / other` and `(self << precision) % other`
  /// *without* overflow or loss of precision (by using a type that's twice as wide as `Self` for
  /// the intermediate computation), provided that `other` is not `0` nor `-1`.
  ///
  /// Returns a tuple (`quotient`, `remainder`).
  ///
  /// # Safety
  ///
  /// If `other` is `Int::0` or `-Int::ONE`, in which case the quotient would be indeterminate or
  /// overflow a `Self`, respectively, calling this function is *undefined behaviour*.
  unsafe fn shift_div_rem(self, other: Self, precision: u32) -> (Self, Self);

  /// Compute the result of a multiword left-shift. The return value is `(hi, lo, index)`, such
  /// that, in terms of infinite precision arithmetic:
  ///
  /// ```ignore
  /// self << n = (hi << Self::BITS + lo) << (8 * index)
  /// ```
  ///
  /// That is, `hi, lo` are the high and low words of the shifted result, and `index` is the offset
  /// in _bytes_, useful if we're representing the multiword number in an array.
  fn multiword_shl(self, n: u32) -> (Self, Self, usize);  // TODO return (Self::Double, usize)
}

// TODO pub trait IntBigEndian

/// This trait models the unsigned counterpart to an [`Int`].
pub trait Unsigned:
  core::fmt::Debug + core::fmt::Display + core::fmt::Binary +
  Copy + Clone +
  Eq + Ord +
  core::ops::Shl<u32, Output=Self> +
  core::ops::Shr<u32, Output=Self> +
{
  fn to_be(self) -> Self;

  fn overflowing_add(self, other: Self) -> (Self, bool);
}

/// This trait models the type that is an `Int` with twice the precision (e.g. `i32::Double` =
/// `i64`). The two ways to convert between the two are by:
///
///   - By multipling two `Int`s with no loss of precision, fitting into a `Double`
///     (`doubling_mul`)
///   - By breaking a `Double` into its hi and lo `Int`s (`components`)
pub trait Double:
  core::fmt::Debug +
  Copy + Clone +
  Eq + Ord +
  core::ops::Shl<u32, Output=Self> +
  core::ops::Shr<u32, Output=Self> +
{
  type Single: Int;

  /// Break a `Double` down into its high and low `Int`s, respectively.
  fn components_hi_lo(self) -> (Self::Single, Self::Single);

  /// See [Sealed::leading_run_minus_one].
  unsafe fn leading_run_minus_one(self) -> u32;
}

mod int;
mod unsigned;
mod double;
mod const_as;
pub use const_as::const_as;
