use super::*;
use crate::underlying::const_i128_as_int;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  /// Zero (`0`), the additive identity element.
  pub const ZERO: Self = Self(Int::ZERO);

  /// NAR is the `0b1000...` bit pattern, appropriately sign-extended. This is that number
  /// represented as an i128 (max width of any Int).
  const NAR_I128: i128 = i128::MIN >> (128 - Int::BITS + Self::JUNK_BITS);

  /// Not-a-real (`NaR`).
  //
  // Represented by the bit pattern `0b1000...0`.
  pub const NAR: Self = Self(const_i128_as_int(Self::NAR_I128));

  /// One (`1`), the additive identity element.
  //
  // Represented by the bit pattern `0b0100...0`.
  pub const ONE: Self = Self(const_i128_as_int(-(Self::NAR_I128 >> 1)));

  /// Negative one (`-1`).
  //
  // Represented by the bit pattern `0b1100...0`.
  pub const MINUS_ONE: Self = Self(const_i128_as_int(Self::NAR_I128 >> 1));

  /// Largest representable value, equal to `-MIN`.
  //
  // Represented by the bit pattern `0b0111...1`.
  pub const MAX: Self = Self(const_i128_as_int(!Self::NAR_I128));

  /// Smallest representable value, equal to `-MAX`.
  ///
  /// Not to be confused with the smallest *absolute value*, i.e. [`Self::MIN_POSITIVE`].
  //
  // Represented by the bit pattern `0b100...01`.
  pub const MIN: Self = Self(const_i128_as_int(Self::NAR_I128 + 1));

  /// Smallest *positive* value, equal to `-MAX_NEGATIVE`.
  //
  // Represented by the bit pattern `0b000...01`.
  pub const MIN_POSITIVE: Self = Self(Int::ONE);

  /// Largest *negative* value, equal to `-MIN_POSITIVE`.
  //
  // Represented by the bit pattern `0b1111...1`.
  pub const MAX_NEGATIVE: Self = Self(const_i128_as_int(-1));

  /// The minimum exponent; [`Self::MIN_POSITIVE`] = 2 <sup>[`Self::MIN_EXP`]</sup>.
  pub const MIN_EXP: Int = {
    let max_regime = N as i128 - 2;
    let min_exp = -(max_regime << ES);
    const_i128_as_int(min_exp)
  };

  /// The maximum exponent; [`Self::MAX_NEGATIVE`] = 2 <sup>[`Self::MAX_EXP`]</sup>.
  pub const MAX_EXP: Int = {
    let max_regime = N as i128 - 2;
    let max_exp = max_regime << ES;
    const_i128_as_int(max_exp)
  };
}

#[cfg(test)]
mod tests {
  use super::*;

  /*#[test]
  fn zero() {
    assert_eq!(Posit::<8,   2, i8  >::ZERO.to_bits(), 0);
    assert_eq!(Posit::<16,  2, i16 >::ZERO.to_bits(), 0);
    assert_eq!(Posit::<32,  2, i32 >::ZERO.to_bits(), 0);
    assert_eq!(Posit::<64,  2, i64 >::ZERO.to_bits(), 0);
    assert_eq!(Posit::<128, 2, i128>::ZERO.to_bits(), 0);

    assert_eq!(Posit::<8,   0, i8  >::ZERO.to_bits(), 0);
    assert_eq!(Posit::<16,  1, i16 >::ZERO.to_bits(), 0);
    assert_eq!(Posit::<32,  2, i32 >::ZERO.to_bits(), 0);
    assert_eq!(Posit::<64,  3, i64 >::ZERO.to_bits(), 0);
    assert_eq!(Posit::<128, 4, i128>::ZERO.to_bits(), 0);

    assert_eq!(Posit::<6, 1, i8>::ZERO.to_bits(), 0);
    assert_eq!(Posit::<10, 2, i64>::ZERO.to_bits(), 0);
    assert_eq!(Posit::<32, 2, i64>::ZERO.to_bits(), 0);
  }*/

  use malachite::rational::Rational;

  #[test]
  fn zero() {
    assert_eq!(
      Posit::<16, 2, i16>::ZERO.to_bits_unsigned(),
      0,
    );
    assert_eq!(
      Posit::<10, 1, i16>::ZERO.to_bits_unsigned(),
      0,
    );
    assert_eq!(
      Rational::try_from(Posit::<10, 1, i16>::ZERO),
      Ok(Rational::from(0)),
    );
  }

  #[test]
  fn nar() {
    assert_eq!(
      Posit::<16, 2, i16>::NAR.to_bits_unsigned(),
      0b1000_0000_0000_0000,
    );
    assert_eq!(
      Posit::<10, 1, i16>::NAR.to_bits_unsigned(),
      0b111111_10_0000_0000,
    );
    assert_eq!(
      Rational::try_from(Posit::<10, 1, i16>::NAR),
      Err(super::rational::IsNaR),
    );
  }

  #[test]
  fn min_positive() {
    assert_eq!(
      Posit::<16, 2, i16>::MIN_POSITIVE.to_bits_unsigned(),
      0b0000_0000_0000_0001,
    );
    assert_eq!(
      Posit::<10, 1, i16>::MIN_POSITIVE.to_bits_unsigned(),
      0b000000_00_0000_0001,
    );
    assert_eq!(
      Rational::try_from(Posit::<10, 1, i16>::MIN_POSITIVE),
      Ok(Rational::from_signeds(1, (1i64 << 2).pow(10 - 2))),
    );
  }

  #[test]
  fn max() {
    assert_eq!(
      Posit::<16, 2, i16>::MAX.to_bits_unsigned(),
      0b0111_1111_1111_1111,
    );
    assert_eq!(
      Posit::<10, 1, i16>::MAX.to_bits_unsigned(),
      0b000000_01_1111_1111,
    );
    assert_eq!(
      Rational::try_from(Posit::<10, 1, i16>::MAX),
      Ok(Rational::from((1i64 << 2).pow(10 - 2))),
    );
  }

  #[test]
  fn max_negative() {
    assert_eq!(
      Posit::<16, 2, i16>::MAX_NEGATIVE.to_bits_unsigned(),
      0b1111_1111_1111_1111,
    );
    assert_eq!(
      Posit::<10, 1, i16>::MAX_NEGATIVE.to_bits_unsigned(),
      0b111111_11_1111_1111,
    );
    assert_eq!(
      Rational::try_from(Posit::<10, 1, i16>::MAX_NEGATIVE),
      Ok(-Rational::from_signeds(1, (1i64 << 2).pow(10 - 2))),
    );
  }

  #[test]
  fn min() {
    assert_eq!(
      Posit::<16, 2, i16>::MIN.to_bits_unsigned(),
      0b1000_0000_0000_0001,
    );
    assert_eq!(
      Posit::<10, 1, i16>::MIN.to_bits_unsigned(),
      0b111111_10_0000_0001,
    );
    assert_eq!(
      Rational::try_from(Posit::<10, 1, i16>::MIN),
      Ok(-Rational::from((1i64 << 2).pow(10 - 2))),
    );
  }

  #[test]
  fn one() {
    assert_eq!(
      Posit::<16, 2, i16>::ONE.to_bits_unsigned(),
      0b0100_0000_0000_0000,
    );
    assert_eq!(
      Posit::<10, 1, i16>::ONE.to_bits_unsigned(),
      0b000000_01_0000_0000,
    );
    assert_eq!(
      Rational::try_from(Posit::<10, 1, i16>::ONE),
      Ok(Rational::from(1)),
    );
  }

  #[test]
  fn minus_one() {
    assert_eq!(
      Posit::<16, 2, i16>::MINUS_ONE.to_bits_unsigned(),
      0b1100_0000_0000_0000,
    );
    assert_eq!(
      Posit::<10, 1, i16>::MINUS_ONE.to_bits_unsigned(),
      0b111111_11_0000_0000,
    );
    assert_eq!(
      Rational::try_from(Posit::<10, 1, i16>::MINUS_ONE),
      Ok(-Rational::from(1)),
    );
  }

  /// Aux function: the max value of an n-bit posit with 2-bit exponent (as per the standard).
  /// max = -min = 1/min_positive = -1/max_negative.
  fn std_max(n: u32) -> Rational {
    use malachite::base::num::arithmetic::traits::PowerOf2;
    let n = i64::from(n);
    Rational::power_of_2(4*n - 8)
  }

  macro_rules! std_tests {
    ($t:ident) => {
      mod $t {
        use super::*;
        use malachite::base::num::arithmetic::traits::Reciprocal;

        #[test]
        fn zero() {
          assert_eq!(crate::$t::ZERO.try_into(), Ok(Rational::from(0)));
        }

        #[test]
        fn nar() {
          assert_eq!(Rational::try_from(crate::$t::NAR), Err(super::rational::IsNaR));
        }

        #[test]
        fn min_positive() {
          assert_eq!(crate::$t::MIN_POSITIVE.try_into(), Ok(std_max(crate::$t::BITS).reciprocal()));
        }

        #[test]
        fn max() {
          assert_eq!(crate::$t::MAX.try_into(), Ok(std_max(crate::$t::BITS)));
        }

        #[test]
        fn max_negative() {
          assert_eq!(crate::$t::MAX_NEGATIVE.try_into(), Ok(-std_max(crate::$t::BITS).reciprocal()));
        }

        #[test]
        fn min() {
          assert_eq!(crate::$t::MIN.try_into(), Ok(-std_max(crate::$t::BITS)));
        }

        #[test]
        fn one() {
          assert_eq!(crate::$t::ONE.try_into(), Ok(Rational::from(1)));
        }

        #[test]
        fn minus_one() {
          assert_eq!(crate::$t::MINUS_ONE.try_into(), Ok(-Rational::from(1)));
        }
      }
    };
  }

  std_tests!{p8}
  std_tests!{p16}
  std_tests!{p32}
  std_tests!{p64}
}