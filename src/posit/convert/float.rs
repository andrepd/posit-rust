use super::*;

use crate::underlying::const_as;

/// Extract the mantissa and exponent fields of an [`f64`], and represent them as a
/// [`Decoded`], plus any sticky bits that have been lost.
fn decode_finite_f64<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
>(num: f64) -> (Decoded<N, ES, Int>, Int) {  // TODO type for `(Decoded, sticky)`
  debug_assert!(num.is_finite());
  const MANTISSA_BITS: u32 = f64::MANTISSA_DIGITS - 1;
  const EXP_BIAS: i64 = f64::MIN_EXP as i64 - 1;
  const HIDDEN_BIT: i64 = (i64::MIN as u64 >> 1) as i64;

  // Extract sign, mantissa, and exponent.
  use crate::underlying::Sealed;
  let sign = num.is_sign_positive();
  let bits = num.abs().to_bits() as i64;
  let mantissa = bits.mask_lsb(MANTISSA_BITS);
  let mut exponent = bits >> MANTISSA_BITS;

  // An exponent field of 0 marks a subnormal number. Normals have implicit unit (`1.xxx`) and -1
  // bias in the exponent; subnormals don't.
  let is_normal = exponent != 0;
  exponent -= i64::from(is_normal);

  // Represent the mantissa as a `frac` in the target type `Int`.
  //
  // First, the float `mantissa` field is (1) unsigned, and (2) does not contain the hidden bit, so
  // we need to correct that. Note that, if `frac` is 1.000… (i.e. `mantissa` = 0), it's negation
  // is not -1.000…, but rather -2.000… with -1 in the `exp`!
  let frac: i64 = {
    const SHIFT_LEFT: u32 = 64 - MANTISSA_BITS - 2;
    let unsigned_frac = (mantissa << SHIFT_LEFT) | HIDDEN_BIT;
    if sign {
      unsigned_frac
    } else if mantissa != 0 {
      -unsigned_frac
    } else {
      exponent -= 1;
      i64::MIN
    }
  };
  // Then, the bits have to be moved, from a width of `i64` to a width of `Int`, which may be
  // either narrower or wider than an `i64`. Bits lost, if any, have to be accumulated onto
  // `sticky`, to be returned.
  let (mut frac, sticky): (Int, Int) = {
    let shift_left = Int::BITS as i64 - 64;
    if shift_left >= 0 {
      // The mantissa has to be shifted left: there are no bits lost.
      let shift_left = shift_left as u32;
      let frac = const_as::<i64, Int>(frac) << shift_left;
      (frac, Int::ZERO)
    } else {
      // The mantissa has to be shifted right: that amount of bits are lost.
      let shift_right = -shift_left as u32;
      let sticky = Int::from(frac.mask_lsb(shift_right) != 0);
      let frac = const_as::<i64, Int>(frac.lshr(shift_right));
      (frac, sticky)
    }
  };

  // If it's a subnormal, then `frac` is "underflowing". We have to find the first 1 after the 0s,
  // or the first 0 after the 1, and shift it to the correct place.
  //
  // Examples:
  //
  //   subnormal frac: 0000001101
  //          becomes: 0110100000 and adjust exponent by -5
  //
  //   subnormal frac: 1111011011
  //          becomes: 1011011000 and adjust exponent by -3
  //
  // Beware also that, if `frac` is exactly 0 (e.g. if some lowest bits have been lost) then we
  // need to floor at `Posit::MIN`.
  if !is_normal {
    if frac == Int::ZERO {
      return (Decoded { frac: Int::ONE, exp: Int::MIN >> 1 }, Int::ZERO)
    }
    // SAFETY: Just early returned if `frac == 0`.
    let underflow = unsafe { frac.leading_run_minus_one() };
    frac = frac << underflow;
    exponent = exponent.wrapping_sub(underflow as i64);
  }

  // Represent the exponent as an `exp` in the target type `Int`.
  //
  // Beware to clamp it to the range representable in a `Decoded::exp` of type `Int`, otherwise
  // there may be overflow in more extreme conversions (like f64 → p8).
  let exponent = exponent.wrapping_add(EXP_BIAS);
  let exp =
    if const { Int::BITS < 64 } && exponent > const_as::<Int, i64>(Int::MAX >> 1) {
      Int::MAX >> 1
    } else if const { Int::BITS < 64 } && exponent < const_as::<Int, i64>(Int::MIN >> 1) {
      Int::MIN >> 1
    } else {
      const_as::<_, Int>(exponent)
    };

  (Decoded { exp, frac }, sticky)
}

/// Extract the mantissa and exponent fields of an [`f64`], and represent them as a
/// [`Decoded`], plus any sticky bits that have been lost.
fn decode_finite_f32<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
>(num: f32) -> (Decoded<N, ES, Int>, Int) {
  debug_assert!(num.is_finite());
  // TODO I'm lazy so for I'm just gonna call into [`decode_finite_f64`], since `f32` → `f64` is
  // lossless; write standalone impl at some point
  decode_finite_f64(num.into())
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> RoundFrom<f32> for Posit<N, ES, Int> {
  /// Convert an `f32` into a `Posit`, [rounding according to the standard]:
  ///
  /// - If the value is any infinity or any NaN, it converts to [NaR](Posit::NAR).
  /// - Otherwise, the float value is rounded (if necessary).
  ///
  /// [rounding according to the standard]: https://posithub.org/docs/posit_standard-2.pdf#subsection.6.5
  fn round_from(value: f32) -> Self {
    use core::num::FpCategory;
    match value.classify() {
      FpCategory::Nan | FpCategory::Infinite => Self::NAR,
      FpCategory::Zero => Self::ZERO,
      FpCategory::Normal | FpCategory::Subnormal => {
        let (decoded, sticky) = decode_finite_f32(value);
        unsafe { decoded.encode_regular_round(sticky) }
      }
    }
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> RoundFrom<f64> for Posit<N, ES, Int> {
  /// Convert an `f64` into a `Posit`, [rounding according to the standard]:
  ///
  /// - If the value is any infinity or any NaN, it converts to [NaR](Posit::NAR).
  /// - Otherwise, the float value is rounded (if necessary).
  ///
  /// [rounding according to the standard]: https://posithub.org/docs/posit_standard-2.pdf#subsection.6.5
  fn round_from(value: f64) -> Self {
    use core::num::FpCategory;
    match value.classify() {
      FpCategory::Nan | FpCategory::Infinite => Self::NAR,
      FpCategory::Zero => Self::ZERO,
      FpCategory::Normal | FpCategory::Subnormal => {
        let (decoded, sticky) = decode_finite_f64(value);
        unsafe { decoded.encode_regular_round(sticky) }
      }
    }
  }
}

/// Take a [`Decoded`] and encode into an [`f64`] using IEEE 754 rounding rules.
fn encode_finite_f64<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
>(decoded: Decoded<N, ES, Int>) -> f64 {
  // Rust assumes that the "default" IEEE rounding mode "roundTiesToEven" is always in effect
  // (anything else is UB). This considerably simplifies this implementation.
  const MANTISSA_BITS: u32 = f64::MANTISSA_DIGITS - 1;
  const EXPONENT_BITS: u32 = 64 - MANTISSA_BITS - 1;

  // Split `frac` into sign and absolute value (sans hidden bit).
  let sign = decoded.frac.is_positive();
  let (frac_abs, exp) =
    // Small detail: a `frac` of `0b10_000…` (= -2.0) is translated to a float mantissa with
    // absolute value 1.0, compensated by adding +1 to the exponent.
    if decoded.frac != Int::MIN {
      (decoded.frac.wrapping_abs().mask_lsb(Decoded::<N, ES, Int>::FRAC_WIDTH), decoded.exp)
    } else {
      (Int::ZERO, decoded.exp + Int::ONE)
    };

  // There are only `EXPONENT_BITS` bits for the exponent, if we overflow this then we have to
  // return ±∞.
  //
  // The range of *normal* f64 numbers has -m < exponent ≤ +m, where `m` is 2^EXPONENT_BITS - 1.
  //
  // However, exponents ≤ -m may still be representable as *subnormal* numbers.
  //
  // We can also short circuit this at compile time by simply checking if Posit::MAX_EXP < m, in
  // which case there's no need to check for overflows or subnormals at all! This is the case,
  // e.g. when converting p8,p16,p32 to f32, or p8,p16,p32,p64 to f64 (so, a common and important
  // case to specialise).
  let max_exponent: i64 = (1 << (EXPONENT_BITS - 1)) - 1;
  let exponent =
    // No overflow possible
    if Int::BITS < EXPONENT_BITS || Posit::<N, ES, Int>::MAX_EXP < const_as(max_exponent) {
      const_as::<Int, i64>(exp)
    }
    // Can overflow
    else {
      // Overflow case, go to infinity
      if exp > const_as(max_exponent) {
        return if sign {f64::INFINITY} else {f64::NEG_INFINITY}
      }
      // Subnormal case, TODO
      else if exp <= const_as(-max_exponent) {
        todo!()
      }
      // Normal case
      else {
        const_as::<Int, i64>(exp)
      }
    };

  // There are only `MANTISSA_BITS` bits for the mantissa, any less than that and we have to do
  // some rounding.
  let shift_left  = MANTISSA_BITS.saturating_sub(Decoded::<N, ES, Int>::FRAC_WIDTH);
  let shift_right = Decoded::<N, ES, Int>::FRAC_WIDTH.saturating_sub(MANTISSA_BITS);
  let mantissa = const_as::<Int, i64>(frac_abs >> shift_right) << shift_left;
  // Compute also the bits lost due to right shift, and compile them into `round` and `sticky`
  // bits.
  //
  // The formula for whether to round up in "round to nearest, ties to even" is the usual one; for
  // more information, look at the comments in [`encode_regular_round`]).
  let lost_bits = if shift_right == 0 {Int::ZERO} else {frac_abs << (Int::BITS - shift_right)};
  let round = lost_bits < Int::ZERO;
  let sticky = lost_bits << 1 != Int::ZERO;
  let odd = mantissa & 1 == 1;
  let round_up = round & (odd | sticky);

  // One detail: if the mantissa overflows (i.e. we rounded up and the mantissa is all 0s), then we
  // need to bump the exponent by 1.
  let mantissa = mantissa + i64::from(round_up);
  let exponent = if round_up & (mantissa == 0) {exponent + 1} else {exponent};

  // Assemble the three fields of the final result: sign, (biased) exponent, and mantissa.
  let bits =
    (u64::from(!sign) << (u64::BITS - 1))
    | (((exponent + max_exponent) as u64) << MANTISSA_BITS)
    | (mantissa as u64);
  f64::from_bits(bits)
}

/// Take a [`Decoded`] and encode into an [`f32`] using IEEE 754 rounding rules.
fn encode_finite_f32<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
>(decoded: Decoded<N, ES, Int>) -> f32 {
  // Again, I'm lazy so shortcut for now.
  encode_finite_f64(decoded) as f32
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> RoundFrom<Posit<N, ES, Int>> for f32 {
  /// Convert a `Posit` into an `f32`, [rounding according to the standard]:
  ///
  /// - If the value is [0](Posit::ZERO), the result is `+0.0`.
  /// - If the value is [NaR](Posit::NAR), the result is a [quiet NaN](f32::NAN).
  /// - Otherwise, the posit value is rounded to a float (if necessary) using the "roundTiesToEven"
  ///   rule in the IEEE 754 standard (in short: underflow to ±0, overflow to ±∞, otherwise round
  ///   to nearest, in case of a tie round to nearest even bit pattern).
  ///
  /// [rounding according to the standard]: https://posithub.org/docs/posit_standard-2.pdf#subsection.6.5
  fn round_from(value: Posit<N, ES, Int>) -> Self {
    if value == Posit::ZERO {
      0.
    } else if value == Posit::NAR {
      f32::NAN
    } else {
      // SAFETY: `value` is not 0 nor NaR
      let decoded = unsafe { value.decode_regular() };
      encode_finite_f32(decoded)
    }
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> RoundFrom<Posit<N, ES, Int>> for f64 {
  /// Convert a `Posit` into an `f64`, [rounding according to the standard]:
  ///
  /// - If the value is [0](Posit::ZERO), the result is `+0.0`.
  /// - If the value is [NaR](Posit::NAR), the result is a [quiet NaN](f64::NAN).
  /// - Otherwise, the posit value is rounded to a float (if necessary) using the "roundTiesToEven"
  ///   rule in the IEEE 754 standard (in short: underflow to ±0, overflow to ±∞, otherwise round
  ///   to nearest, in case of a tie round to nearest even bit pattern).
  ///
  /// [rounding according to the standard]: https://posithub.org/docs/posit_standard-2.pdf#subsection.6.5
  fn round_from(value: Posit<N, ES, Int>) -> Self {
    if value == Posit::ZERO {
      0.
    } else if value == Posit::NAR {
      f64::NAN
    } else {
      // SAFETY: `value` is not 0 nor NaR
      let decoded = unsafe { value.decode_regular() };
      encode_finite_f64(decoded)
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use malachite::rational::Rational;
  use proptest::prelude::*;

  mod float_to_posit {
    use super::*;

    /// Instantiate a suite of tests
    macro_rules! make_tests {
      ($float:ty, $posit:ty) => {
        use super::*;

        #[test]
        fn zero() {
          assert_eq!(<$posit>::round_from(0.0 as $float), <$posit>::ZERO)
        }

        #[test]
        fn one() {
          assert_eq!(<$posit>::round_from(1.0 as $float), <$posit>::ONE)
        }

        #[test]
        fn minus_one() {
          assert_eq!(<$posit>::round_from(-1.0 as $float), <$posit>::MINUS_ONE)
        }

        #[test]
        fn nan() {
          assert_eq!(<$posit>::round_from(<$float>::NAN), <$posit>::NAR)
        }

        #[test]
        fn min() {
          if const { <$posit>::MAX_EXP as i64 <= 127 } {
            assert_eq!(<$posit>::round_from(<$float>::MIN), <$posit>::MIN)
          }
        }

        #[test]
        fn max() {
          if const { <$posit>::MAX_EXP as i64 <= 127 } {
            assert_eq!(<$posit>::round_from(<$float>::MAX), <$posit>::MAX)
          }
        }

        #[test]
        fn min_positive() {
          if const { <$posit>::MAX_EXP as i64 <= 127 } {
            assert_eq!(<$posit>::round_from(<$float>::MIN_POSITIVE), <$posit>::MIN_POSITIVE)
          }
        }

        #[test]
        fn max_negative() {
          if const { <$posit>::MAX_EXP as i64 <= 127 } {
            assert_eq!(<$posit>::round_from(-<$float>::MIN_POSITIVE), <$posit>::MAX_NEGATIVE)
          }
        }

        #[test]
        fn subnormal_positive() {
          if const { <$posit>::MAX_EXP as i64 <= 127 } {
            assert_eq!(<$posit>::round_from(<$float>::from_bits(1)), <$posit>::MIN_POSITIVE)
          }
        }

        #[test]
        fn subnormal_negative() {
          if const { <$posit>::MAX_EXP as i64 <= 127 } {
            assert_eq!(<$posit>::round_from(-<$float>::from_bits(1)), <$posit>::MAX_NEGATIVE)
          }
        }

        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
          #[test]
          fn proptest(float: $float) {
            let posit = <$posit>::round_from(float);
            match Rational::try_from(float) {
              Ok(exact) => assert!(super::rational::is_correct_rounded(exact, posit)),
              Err(_) => assert!(posit == <$posit>::NAR),
            }
          }
        }
      };
    }

    mod f64 {
      use super::*;

      mod p8 { make_tests!{f64, crate::p8} }
      mod p16 { make_tests!{f64, crate::p16} }
      mod p32 { make_tests!{f64, crate::p32} }
      mod p64 { make_tests!{f64, crate::p64} }

      mod posit_8_0 { make_tests!{f64, Posit::<8, 0, i8>} }
      mod posit_10_0 { make_tests!{f64, Posit::<10, 0, i16>} }
      mod posit_10_1 { make_tests!{f64, Posit::<10, 1, i16>} }
      mod posit_10_2 { make_tests!{f64, Posit::<10, 2, i16>} }
      mod posit_10_3 { make_tests!{f64, Posit::<10, 3, i16>} }
      mod posit_20_4 { make_tests!{f64, Posit::<20, 4, i32>} }

      mod posit_3_0 { make_tests!{f64, Posit::<3, 0, i8>} }
      mod posit_4_0 { make_tests!{f64, Posit::<4, 0, i8>} }
      mod posit_4_1 { make_tests!{f64, Posit::<4, 1, i8>} }
    }

    mod f32 {
      use super::*;

      mod p8 { make_tests!{f32, crate::p8} }
      mod p16 { make_tests!{f32, crate::p16} }
      mod p32 { make_tests!{f32, crate::p32} }
      mod p64 { make_tests!{f32, crate::p64} }

      mod posit_8_0 { make_tests!{f32, Posit::<8, 0, i8>} }
      mod posit_10_0 { make_tests!{f32, Posit::<10, 0, i16>} }
      mod posit_10_1 { make_tests!{f32, Posit::<10, 1, i16>} }
      mod posit_10_2 { make_tests!{f32, Posit::<10, 2, i16>} }
      mod posit_10_3 { make_tests!{f32, Posit::<10, 3, i16>} }
      mod posit_20_4 { make_tests!{f32, Posit::<20, 4, i32>} }

      mod posit_3_0 { make_tests!{f32, Posit::<3, 0, i8>} }
      mod posit_4_0 { make_tests!{f32, Posit::<4, 0, i8>} }
      mod posit_4_1 { make_tests!{f32, Posit::<4, 1, i8>} }
    }
  }

  mod posit_to_float {
    use super::*;

    // TODO Tests are very incomplete! It's limited to testing float ↔ posit roundtrips, which is
    // not even exact!

    /// Instantiate a suite of tests
    macro_rules! test_exhaustive {
      ($float:ty, $posit:ty) => {
        use super::*;

        #[test]
        fn posit_roundtrip_exhaustive() {
          for posit in <$posit>::cases_exhaustive_all() {
            let float = <$float>::round_from(posit);
            let reposit = <$posit>::round_from(float);
            assert_eq!(posit, reposit)
          }
        }

        /*#[test]
        fn float_roundtrip_exhaustive(float: $float) {
          let posit = <$posit>::round_from(float);
          let refloat = <$float>::round_from(posit);
          assert_eq!(float, refloat)
        }*/
      };
    }

    /// Instantiate a suite of tests
    macro_rules! test_proptest {
      ($float:ty, $posit:ty) => {
        use super::*;

        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]

          #[test]
          fn posit_roundtrip_proptest(posit in <$posit>::cases_proptest_all()) {
            let float = <$float>::round_from(posit);
            let reposit = <$posit>::round_from(float);
            assert_eq!(posit, reposit)
          }

          /*#[test]
          fn float_roundtrip_proptest(float: $float) {
            let posit = <$posit>::round_from(float);
            let refloat = <$float>::round_from(posit);
            assert_eq!(float, refloat)
          }*/
        }
      };
    }

    mod f64 {
      use super::*;

      mod p8 { test_exhaustive!{f64, crate::p8} }
      mod p16 { test_exhaustive!{f64, crate::p16} }
      mod p32 { test_proptest!{f64, crate::p32} }
      // mod p64 { test_proptest!{f64, crate::p64} }

      mod posit_8_0 { test_exhaustive!{f64, Posit::<8, 0, i8>} }
      mod posit_10_0 { test_exhaustive!{f64, Posit::<10, 0, i16>} }
      mod posit_10_1 { test_exhaustive!{f64, Posit::<10, 1, i16>} }
      mod posit_10_2 { test_exhaustive!{f64, Posit::<10, 2, i16>} }
      mod posit_10_3 { test_exhaustive!{f64, Posit::<10, 3, i16>} }
      mod posit_20_4 { test_proptest!{f64, Posit::<20, 4, i32>} }

      mod posit_3_0 { test_exhaustive!{f64, Posit::<3, 0, i8>} }
      mod posit_4_0 { test_exhaustive!{f64, Posit::<4, 0, i8>} }
      mod posit_4_1 { test_exhaustive!{f64, Posit::<4, 1, i8>} }
    }

    mod f32 {
      use super::*;

      mod p8 { test_exhaustive!{f32, crate::p8} }
      mod p16 { test_exhaustive!{f32, crate::p16} }
      // mod p32 { test_proptest!{f32, crate::p32} }
      // mod p64 { test_proptest!{f32, crate::p64} }

      mod posit_8_0 { test_exhaustive!{f32, Posit::<8, 0, i8>} }
      mod posit_10_0 { test_exhaustive!{f32, Posit::<10, 0, i16>} }
      mod posit_10_1 { test_exhaustive!{f32, Posit::<10, 1, i16>} }
      mod posit_10_2 { test_exhaustive!{f32, Posit::<10, 2, i16>} }
      mod posit_10_3 { test_exhaustive!{f32, Posit::<10, 3, i16>} }
      // mod posit_20_4 { test_proptest!{f32, Posit::<20, 4, i32>} }

      mod posit_3_0 { test_exhaustive!{f32, Posit::<3, 0, i8>} }
      mod posit_4_0 { test_exhaustive!{f32, Posit::<4, 0, i8>} }
      mod posit_4_1 { test_exhaustive!{f32, Posit::<4, 1, i8>} }
    }
  }
}
