use super::*;
use crate::underlying::const_as;

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
  pub const NAR: Self = Self(const_as(Self::NAR_I128));

  /// One (`1`), the additive identity element.
  //
  // Represented by the bit pattern `0b0100...0`.
  pub const ONE: Self = Self(const_as(-(Self::NAR_I128 >> 1)));

  /// Negative one (`-1`).
  //
  // Represented by the bit pattern `0b1100...0`.
  pub const MINUS_ONE: Self = Self(const_as(Self::NAR_I128 >> 1));

  /// Greatest representable value, equal to `-MIN`.
  //
  // Represented by the bit pattern `0b0111...1`.
  pub const MAX: Self = Self(const_as(!Self::NAR_I128));

  /// Smallest representable value, equal to `-MAX`.
  ///
  /// Not to be confused with the smallest *absolute value*, i.e. [`Self::MIN_POSITIVE`].
  //
  // Represented by the bit pattern `0b100...01`.
  pub const MIN: Self = Self(const_as(Self::NAR_I128 + 1));

  /// Smallest *positive* value, equal to `-MAX_NEGATIVE`.
  //
  // Represented by the bit pattern `0b000...01`.
  pub const MIN_POSITIVE: Self = Self(Int::ONE);

  /// Largest *negative* value, equal to `-MIN_POSITIVE`.
  //
  // Represented by the bit pattern `0b1111...1`.
  pub const MAX_NEGATIVE: Self = Self(const_as(-1));

  /// The largest *consecutive* integer value, that is: integers in the range `0 ..= Self::INT_MAX`
  /// are exactly representable as a posit of this type.
  ///
  /// Standard: "[**pIntMax**](https://posithub.org/docs/posit_standard-2.pdf#subsection.3.2)".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(p8::INT_MAX, 1 << 4);
  /// assert_eq!(p16::INT_MAX, 1 << 10);
  /// assert_eq!(p32::INT_MAX, 1 << 23);
  /// assert_eq!(p64::INT_MAX, 1 << 48);
  /// ```
  pub const INT_MAX: Int = Self::int_max();

  const fn int_max() -> Int {
    // If a (positive) power of two is representable as a posit, it looks like this:
    //
    //   0b0_11…10_ee_000000…
    //
    // A 0 sign bit, a positive `regime` represented by a sequence of `regime + 1` 1s terminated by
    // a 0, then `ES` exponent bits, then 0s all the way through the end for the fraction bits.
    //
    // To figure out what's the maximum integer such that all numbers from 0 to that integer are
    // exactly representable as a posit, let's work by induction by thinking like this: the number
    // `1` is always representable as a posit. Then, if a positive power of two `1 << power` is
    // representable as a posit, the next number is representable if
    //
    //   0b0_11…10_ee_000…001000…
    //
    // is representable as a posit, where there are `power - 1` 0s in the fraction before the 1.
    //
    // If this is the case, then all the numbers up to the next power of two are also representable
    //
    //   0b0_11…10_ee_000…010000…
    //   0b0_11…10_ee_000…011000…
    //   0b0_11…10_ee_000…100000…
    //   …
    //
    // But we also know that the number of fraction bits is `N - 1 - (regime + 1) - 1 - ES`.
    // Therefore, if this number is smaller than `power`, then we cannot represent the integer
    // after `1 << power` as a posit without rounding, meaning `1 << power` is the largest
    // consecutive integer representable as this posit.
    //
    // So we just iterate through powers of two until we find the biggest representable `power`;
    // the answer is `1 << power`.
    let mut power = 0;
    while power < Int::BITS {
      let regime = power >> ES;
      // If not even enough bits to represent the regime and exponent fields, this is `INT_MAX`.
      if Self::BITS < regime + ES + 3 {
        return const_as::<i128, Int>(1 << power)
      }
      // Otherwise we have `fraction_bits` left over, if we cannot represent the next integer, this
      // is `INT_MAX`.
      let fraction_bits = Self::BITS - regime - ES - 3;
      if fraction_bits < power {
        return const_as::<i128, Int>(1 << power)
      }
      power += 1
    }
    unreachable!()
  }

  /// The maximum exponent; [`Self::MAX`] = 2 <sup>[`Self::MAX_EXP`]</sup>. Equal to `-MIN_EXP`.
  pub(crate) const MAX_EXP: Int = {
    let max_regime = N as i128 - 2;
    let max_exp = max_regime << ES;
    const_as(max_exp)
  };

  /// The minimum exponent; [`Self::MIN_POSITIVE`] = 2 <sup>[`Self::MIN_EXP`]</sup>. Equal to
  /// `-MAX_EXP`.
  pub(crate) const MIN_EXP: Int = {
    let max_regime = N as i128 - 2;
    let min_exp = -(max_regime << ES);
    const_as(min_exp)
  };
}

#[cfg(test)]
#[allow(overflowing_literals)]
mod tests {
  use super::*;

  use malachite::rational::Rational;

  #[test]
  fn zero() {
    assert_eq!(
      Posit::<16, 2, i16>::ZERO.to_bits(),
      0,
    );
    assert_eq!(
      Posit::<10, 1, i16>::ZERO.to_bits(),
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
      Posit::<16, 2, i16>::NAR.to_bits(),
      0b1000_0000_0000_0000,
    );
    assert_eq!(
      Posit::<10, 1, i16>::NAR.to_bits(),
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
      Posit::<16, 2, i16>::MIN_POSITIVE.to_bits(),
      0b0000_0000_0000_0001,
    );
    assert_eq!(
      Posit::<10, 1, i16>::MIN_POSITIVE.to_bits(),
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
      Posit::<16, 2, i16>::MAX.to_bits(),
      0b0111_1111_1111_1111,
    );
    assert_eq!(
      Posit::<10, 1, i16>::MAX.to_bits(),
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
      Posit::<16, 2, i16>::MAX_NEGATIVE.to_bits(),
      0b1111_1111_1111_1111,
    );
    assert_eq!(
      Posit::<10, 1, i16>::MAX_NEGATIVE.to_bits(),
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
      Posit::<16, 2, i16>::MIN.to_bits(),
      0b1000_0000_0000_0001,
    );
    assert_eq!(
      Posit::<10, 1, i16>::MIN.to_bits(),
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
      Posit::<16, 2, i16>::ONE.to_bits(),
      0b0100_0000_0000_0000,
    );
    assert_eq!(
      Posit::<10, 1, i16>::ONE.to_bits(),
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
      Posit::<16, 2, i16>::MINUS_ONE.to_bits(),
      0b1100_0000_0000_0000,
    );
    assert_eq!(
      Posit::<10, 1, i16>::MINUS_ONE.to_bits(),
      0b111111_11_0000_0000,
    );
    assert_eq!(
      Rational::try_from(Posit::<10, 1, i16>::MINUS_ONE),
      Ok(-Rational::from(1)),
    );
  }

  #[test]
  fn int_max() {
    fn exhaustive<const N: u32, const ES: u32, Int: crate::Int>() {
      use crate::RoundInto;
      // All numbers from 0 to INT_MAX round-trip losslessly to posit
      let int_max: i32 = const_as(Posit::<N, ES, Int>::INT_MAX);
      for int in 0 ..= int_max {
        let posit: Posit::<N, ES, Int> = int.round_into();
        let re_int: i32 = posit.round_into();
        assert_eq!(int, re_int)
      }
      // The number immediately after doesn't
      let int_invalid: i32 = int_max + 1;
      let posit_invalid: Posit::<N, ES, Int> = int_invalid.round_into();
      let re_int_invalid: i32 = posit_invalid.round_into();
      assert_ne!(int_invalid, re_int_invalid)
    }

    exhaustive::<10, 0, i16>();
    exhaustive::<10, 1, i16>();
    exhaustive::<10, 2, i16>();
    exhaustive::<10, 3, i16>();
    exhaustive::<8, 0, i8>();
    exhaustive::<8, 2, i8>();
    exhaustive::<16, 2, i16>();
    exhaustive::<32, 2, i32>();
    exhaustive::<32, 2, i32>();
    exhaustive::<3, 0, i8>();
    exhaustive::<4, 0, i8>();
    exhaustive::<4, 1, i8>();
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