use super::*;
use crate::underlying::const_i128_as_int;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  /// The size of this Posit type in bits.
  ///
  /// Note: this is the logical size, not necessarily the size of the underlying type.
  pub const BITS: u32 = {
    assert!(
      N >= 3,
      "A posit cannot have fewer than 3 bits",
    );
    assert!(
      N <= Int::BITS,
      "Cannot represent an n-bit Posit with an underlying Int machine type with fewer bits.",
    );
    N
  };

  /// The number of exponent bits.
  pub const ES: u32 = {
    assert!(
      ES <= N,
      "Cannot use a number of exponent bits ES higher than the number of total bits N",
    );
    // The value of ES isn't completely arbitrary. Very extreme values of ES would cause the maximum
    // exponent to overflow the width of the `Int` type. Therefore, we check this at compile-time.
    //
    // The maximum exponent is 2 ^ Self::MAX_EXP. However, for guarding against overflow in all
    // operations in the Posit standard, it's also really helpful to represent quantities up to
    // (2 ^ Self::MAX_EXP) ^ 3 = 2 ^ (3 * Self::MAX_EXP). Rounding up to a clean number, we require
    // the number 4 * Self::MAX_EXP (exclusive) to be representable in an `Int`.
    //
    // Self::MAX_EXP is (N-2) * 2^ES, so our requirement is 4 * (N-2) * 2^ES < 2 ^ Int::BITS, or
    // N - 2 < 2 ^ (Int::BITS - ES - 2).
    //
    // To make Rust allow this to go in compile-time (const), we round (N-2) down to the nearest
    // power of two and take the log, i.e. we check 2 ^ floor(log(N-2)) < 2 ^ (Int::BITS - ES - 2)
    // or finally floor(log(N-2)) < Int::BITS - ES - 2.
    assert!(
      (N - 2).ilog2() + ES + 2 < Int::BITS,
      "The chosen ES is too big for this combination of N and underlying Int type. Consider \
      lowering the number of exponent bits, or choosing a bigger underlying Int if you really \
      want this many.",
    );
    ES
  };

  /// When representing an `N`-bit posit using a machine type whose width is `M`, the leftmost
  /// `N - M` bits are junk; they are always the same as the bit `N-1` (the function
  /// [`Self::sign_extend`] maintains this invariant).
  ///
  /// In other words, the range of the `Int` in `Posit<N, ES, Int>` is from `-2^N` to `+2^N - 1`.
  ///
  /// Of course, if [`Self::BITS`] is exactly as wide as the underlying `Int::BITS` (as is vastly
  /// the more common case), this is `0`.
  pub(crate) const JUNK_BITS: u32 = Int::BITS - Self::BITS;

  /// Take an `Int` and sign-extend from [`Self::BITS`] (logical width of posit) to `Int::BITS`.
  #[inline]
  pub(crate) /*const*/ fn sign_extend(x: Int) -> Int {
    if const { Self::JUNK_BITS == 0 } {
      x
    } else {
      (x << Self::JUNK_BITS) >> Self::JUNK_BITS
    }
  }

  /// Construct a posit from its raw bit representation. Bits higher (more significant) than the
  /// lowest N ([`Self::BITS`]) bits, if any, are ignored.
  pub /*const*/ fn from_bits(x: Int) -> Self {
    Self(Self::sign_extend(x))
  }

  /// As [Self::from_bits], but if `x` is not a result of a [`Self::to_bits`] call, then calling
  /// this function is undefined behaviour.
  pub const unsafe fn from_bits_unchecked(x: Int) -> Self {
    Self(x)
  }

  /// Return the underlying bit representation of `self` as a machine int. Bits higher
  /// (more significant) than the lowest N ([`Self::BITS`]) bits, if any, are set as equal to the
  /// N-1th bit (i.e. sign-extended).
  pub const fn to_bits(self) -> Int {
    self.0
  }

  #[inline]
  pub(crate) fn from_bits_unsigned(x: Int::Unsigned) -> Self {
    Self::from_bits(Int::of_unsigned(x))
  }

  #[inline]
  pub(crate) fn to_bits_unsigned(self) -> Int::Unsigned {
    self.to_bits().as_unsigned()
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Decoded<N, ES, Int> {
  /// The [Decoded::frac] field represents the fraction / mantissa of a posit as a fixed-point
  /// number, with absolute value between 1 and 2.
  ///
  /// What this means is that an (integer) number `frac` represents the (rational) number `frac` /
  /// `FRAC_DENOM`, where `FRAC_DENOM` is the bit pattern `0b01000...`. For instance
  ///
  ///   | `frac`        | rational value |
  ///   | `0b01_000000` | +1             |
  ///   | `0b01_100000` | +1.5           |
  ///   | `0b01_010000` | +1.25          |
  ///   | `0b10_010000` | -1.75          |
  ///   | `0b10_110000` | -1.25          |
  ///
  /// and so on.
  pub(crate) const FRAC_DENOM: Int = const_i128_as_int(1 << (Int::BITS - 2));

  /// The size of this Posit type in bits.
  ///
  /// Note: this is the logical size, not necessarily the size of the underlying type.
  pub const BITS: u32 = Posit::<N, ES, Int>::BITS;

  /// The number of exponent bits.
  pub const ES: u32 = Posit::<N, ES, Int>::ES;

  /// Checks whether `self` is normalised, i.e. whether `self.frac` starts with `0b01` or `0b10`.
  pub(crate) fn is_normalised(self) -> bool {
    let x = self.frac >> (Int::BITS - 2);
    x == Int::ONE || x == !Int::ONE
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn bits() {
    assert_eq!(Posit::<8, 2, i8>::BITS, 8);
    assert_eq!(Posit::<16, 2, i16>::BITS, 16);
    assert_eq!(Posit::<32, 2, i32>::BITS, 32);
    assert_eq!(Posit::<64, 2, i64>::BITS, 64);
    assert_eq!(Posit::<128, 2, i128>::BITS, 128);

    assert_eq!(Posit::<8, 0, i8>::BITS, 8);
    assert_eq!(Posit::<16, 1, i16>::BITS, 16);
    assert_eq!(Posit::<32, 2, i32>::BITS, 32);
    assert_eq!(Posit::<64, 3, i64>::BITS, 64);
    assert_eq!(Posit::<128, 4, i128>::BITS, 128);

    assert_eq!(Posit::<6, 1, i8>::BITS, 6);
    assert_eq!(Posit::<10, 2, i64>::BITS, 10);
    assert_eq!(Posit::<32, 2, i64>::BITS, 32);
  }

  #[test]
  fn es() {
    assert_eq!(Posit::<8, 2, i8>::ES, 2);
    assert_eq!(Posit::<16, 2, i16>::ES, 2);
    assert_eq!(Posit::<32, 2, i32>::ES, 2);
    assert_eq!(Posit::<64, 2, i64>::ES, 2);
    assert_eq!(Posit::<128, 2, i128>::ES, 2);

    assert_eq!(Posit::<8, 0, i8>::ES, 0);
    assert_eq!(Posit::<16, 1, i16>::ES, 1);
    assert_eq!(Posit::<32, 2, i32>::ES, 2);
    assert_eq!(Posit::<64, 3, i64>::ES, 3);
    assert_eq!(Posit::<128, 4, i128>::ES, 4);

    assert_eq!(Posit::<6, 1, i8>::ES, 1);
    assert_eq!(Posit::<10, 2, i64>::ES, 2);
    assert_eq!(Posit::<32, 2, i64>::ES, 2);
  }

  #[test]
  fn es_max() {
    assert_eq!(Posit::<8, 3, i8>::ES, 3);
    assert_eq!(Posit::<16, 10, i16>::ES, 10);
    assert_eq!(Posit::<32, 25, i32>::ES, 25);
    assert_eq!(Posit::<64, 56, i64>::ES, 56);
    assert_eq!(Posit::<128, 119, i128>::ES, 119);

    assert_eq!(Posit::<8, 8, i16>::ES, 8);
    assert_eq!(Posit::<16, 16, i32>::ES, 16);
    assert_eq!(Posit::<32, 32, i64>::ES, 32);
    assert_eq!(Posit::<64, 64, i128>::ES, 64);
  }

  #[test]
  fn from_bits() {
    fn assert_roundtrip<const N: u32, const ES: u32, Int: crate::Int>(a: Int::Unsigned, b: Int::Unsigned) {
      use super::*;
      assert_eq!(
        Posit::<N, ES, Int>::from_bits_unsigned(a).to_bits(),
        Int::of_unsigned(b),
      )
    }

    // N = width of type
    assert_roundtrip::<16, 2, i16>(
      0b0000_0101_0011_1010,
      0b0000_0101_0011_1010,
    );
    assert_roundtrip::<16, 2, i16>(
      0b1111_0101_0011_1010,
      0b1111_0101_0011_1010,
    );
    assert_roundtrip::<16, 2, i16>(
      0b0101_0011_0011_1010,
      0b0101_0011_0011_1010,
    );

    // N < width of type (needs sign-extension to bits ≥ 10)
    assert_roundtrip::<10, 2, i16>(
      0b000001_01_0011_1010,
      0b000000_01_0011_1010,
    );
    assert_roundtrip::<10, 2, i16>(
      0b111101_01_0011_1010,
      0b000000_01_0011_1010,
    );
    assert_roundtrip::<10, 2, i16>(
      0b010100_11_0011_1010,
      0b111111_11_0011_1010,
    );
  }
}

mod tests_compile_fail {
  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<2, 0, i8>::BITS }
  /// ```
  #[allow(dead_code)]
  fn bits_fail_8_few() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<2, 1, i16>::BITS }
  /// ```
  #[allow(dead_code)]
  fn bits_fail_16_few() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<2, 2, i32>::BITS }
  /// ```
  #[allow(dead_code)]
  fn bits_fail_32_few() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<2, 3, i64>::BITS }
  /// ```
  #[allow(dead_code)]
  fn bits_fail_64_few() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<2, 4, i128>::BITS }
  /// ```
  #[allow(dead_code)]
  fn bits_fail_128_few() {}

  //

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<9, 0, i8>::BITS }
  /// ```
  #[allow(dead_code)]
  fn bits_fail_8_many() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<17, 1, i16>::BITS }
  /// ```
  #[allow(dead_code)]
  fn bits_fail_16_many() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<33, 2, i32>::BITS }
  /// ```
  #[allow(dead_code)]
  fn bits_fail_32_many() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<65, 3, i64>::BITS }
  /// ```
  #[allow(dead_code)]
  fn bits_fail_64_many() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<129, 4, i128>::BITS }
  /// ```
  #[allow(dead_code)]
  fn bits_fail_128_many() {}

  //

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<8, 4, i8>::ES }
  /// ```
  #[allow(dead_code)]
  fn es_fail_8_many() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<16, 11, i16>::ES }
  /// ```
  #[allow(dead_code)]
  fn es_fail_16_many() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<32, 26, i32>::ES }
  /// ```
  #[allow(dead_code)]
  fn es_fail_32_many() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<64, 57, i64>::ES }
  /// ```
  #[allow(dead_code)]
  fn es_fail_64_many() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<128, 120, i128>::ES }
  /// ```
  #[allow(dead_code)]
  fn es_fail_128_many() {}

  //

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<8, 9, i16>::ES }
  /// ```
  #[allow(dead_code)]
  fn es_fail_8_larger() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<16, 17, i32>::ES }
  /// ```
  #[allow(dead_code)]
  fn es_fail_16_larger() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<32, 33, i64>::ES }
  /// ```
  #[allow(dead_code)]
  fn es_fail_32_larger() {}

  /// ```compile_fail
  /// use soft_posit::Posit;
  /// pub fn foo() -> u32 { Posit::<64, 65, i128>::ES }
  /// ```
  #[allow(dead_code)]
  fn es_fail_64_larger() {}
}
