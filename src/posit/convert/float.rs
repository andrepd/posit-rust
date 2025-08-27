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
  const MANTISSA_DIGITS_EXPLICIT: u32 = f64::MANTISSA_DIGITS - 1;
  const EXP_BIAS: i64 = f64::MIN_EXP as i64 - 1;
  const HIDDEN_BIT: i64 = (i64::MIN as u64 >> 1) as i64;

  // Extract sign, mantissa, and exponent.
  use crate::underlying::Sealed;
  let sign = num.is_sign_positive();
  let bits = num.abs().to_bits() as i64;
  let mantissa = bits.mask_lsb(MANTISSA_DIGITS_EXPLICIT);
  let mut exponent = bits >> MANTISSA_DIGITS_EXPLICIT;

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
    const SHIFT_LEFT: u32 = 64 - MANTISSA_DIGITS_EXPLICIT - 2;
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
  /// - If the value is any infinity or any NaN, it converts to [`NaR`](Posit::NAR).
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
  /// - If the value is any infinity or any NaN, it converts to [`NaR`](Posit::NAR).
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

#[cfg(test)]
mod tests {
  use super::*;

  use malachite::rational::Rational;
  use proptest::prelude::*;

  mod f64 {
    use super::*;

    /// Aux function: check that `float` is converted to a posit with the correct rounding.
    fn is_correct_rounded<const N: u32, const ES: u32, Int: crate::Int>(float: f64) -> bool
    where
      Rational: From<Decoded<N, ES, Int>> + TryFrom<Posit<N, ES, Int>> + TryFrom<f64>,
      <Rational as TryFrom<Posit<N, ES, Int>>>::Error: core::fmt::Debug
    {
      let posit = Posit::<N, ES, Int>::round_from(float);
      match Rational::try_from(float) {
        Ok(exact) => super::rational::is_correct_rounded(exact, posit),
        Err(_) => posit == Posit::NAR,
      }
    }

    #[test]
    fn zero() {
      assert_eq!(crate::p8::round_from(0.0f64), crate::p8::ZERO);
      assert_eq!(crate::p16::round_from(0.0f64), crate::p16::ZERO);
      assert_eq!(crate::p32::round_from(0.0f64), crate::p32::ZERO);
      assert_eq!(crate::p64::round_from(0.0f64), crate::p64::ZERO);
      assert_eq!(Posit::<8, 0, i8>::round_from(0.0f64), Posit::<8, 0, i8>::ZERO);
      assert_eq!(Posit::<10, 0, i16>::round_from(0.0f64), Posit::<10, 0, i16>::ZERO);
      assert_eq!(Posit::<10, 1, i16>::round_from(0.0f64), Posit::<10, 1, i16>::ZERO);
      assert_eq!(Posit::<10, 2, i16>::round_from(0.0f64), Posit::<10, 2, i16>::ZERO);
      assert_eq!(Posit::<10, 3, i16>::round_from(0.0f64), Posit::<10, 3, i16>::ZERO);
    }

    #[test]
    fn one() {
      assert_eq!(crate::p8::round_from(1.0f64), crate::p8::ONE);
      assert_eq!(crate::p16::round_from(1.0f64), crate::p16::ONE);
      assert_eq!(crate::p32::round_from(1.0f64), crate::p32::ONE);
      assert_eq!(crate::p64::round_from(1.0f64), crate::p64::ONE);
      assert_eq!(Posit::<8, 0, i8>::round_from(1.0f64), Posit::<8, 0, i8>::ONE);
      assert_eq!(Posit::<10, 0, i16>::round_from(1.0f64), Posit::<10, 0, i16>::ONE);
      assert_eq!(Posit::<10, 1, i16>::round_from(1.0f64), Posit::<10, 1, i16>::ONE);
      assert_eq!(Posit::<10, 2, i16>::round_from(1.0f64), Posit::<10, 2, i16>::ONE);
      assert_eq!(Posit::<10, 3, i16>::round_from(1.0f64), Posit::<10, 3, i16>::ONE);
    }

    #[test]
    fn minus_one() {
      assert_eq!(crate::p8::round_from(-1.0f64), crate::p8::MINUS_ONE);
      assert_eq!(crate::p16::round_from(-1.0f64), crate::p16::MINUS_ONE);
      assert_eq!(crate::p32::round_from(-1.0f64), crate::p32::MINUS_ONE);
      assert_eq!(crate::p64::round_from(-1.0f64), crate::p64::MINUS_ONE);
      assert_eq!(Posit::<8, 0, i8>::round_from(-1.0f64), Posit::<8, 0, i8>::MINUS_ONE);
      assert_eq!(Posit::<10, 0, i16>::round_from(-1.0f64), Posit::<10, 0, i16>::MINUS_ONE);
      assert_eq!(Posit::<10, 1, i16>::round_from(-1.0f64), Posit::<10, 1, i16>::MINUS_ONE);
      assert_eq!(Posit::<10, 2, i16>::round_from(-1.0f64), Posit::<10, 2, i16>::MINUS_ONE);
      assert_eq!(Posit::<10, 3, i16>::round_from(-1.0f64), Posit::<10, 3, i16>::MINUS_ONE);
    }

    #[test]
    fn nan() {
      assert_eq!(crate::p8::round_from(f64::NAN), crate::p8::NAR);
      assert_eq!(crate::p16::round_from(f64::NAN), crate::p16::NAR);
      assert_eq!(crate::p32::round_from(f64::NAN), crate::p32::NAR);
      assert_eq!(crate::p64::round_from(f64::NAN), crate::p64::NAR);
      assert_eq!(Posit::<8, 0, i8>::round_from(f64::NAN), Posit::<8, 0, i8>::NAR);
      assert_eq!(Posit::<10, 0, i16>::round_from(f64::NAN), Posit::<10, 0, i16>::NAR);
      assert_eq!(Posit::<10, 1, i16>::round_from(f64::NAN), Posit::<10, 1, i16>::NAR);
      assert_eq!(Posit::<10, 2, i16>::round_from(f64::NAN), Posit::<10, 2, i16>::NAR);
      assert_eq!(Posit::<10, 3, i16>::round_from(f64::NAN), Posit::<10, 3, i16>::NAR);
    }

    #[test]
    fn min_positive() {
      assert_eq!(crate::p8::round_from(f64::MIN_POSITIVE), crate::p8::MIN_POSITIVE);
      assert_eq!(crate::p16::round_from(f64::MIN_POSITIVE), crate::p16::MIN_POSITIVE);
      assert_eq!(crate::p32::round_from(f64::MIN_POSITIVE), crate::p32::MIN_POSITIVE);
      assert_eq!(crate::p64::round_from(f64::MIN_POSITIVE), crate::p64::MIN_POSITIVE);
      assert_eq!(Posit::<8, 0, i8>::round_from(f64::MIN_POSITIVE), Posit::<8, 0, i8>::MIN_POSITIVE);
      assert_eq!(Posit::<10, 0, i16>::round_from(f64::MIN_POSITIVE), Posit::<10, 0, i16>::MIN_POSITIVE);
      assert_eq!(Posit::<10, 1, i16>::round_from(f64::MIN_POSITIVE), Posit::<10, 1, i16>::MIN_POSITIVE);
      assert_eq!(Posit::<10, 2, i16>::round_from(f64::MIN_POSITIVE), Posit::<10, 2, i16>::MIN_POSITIVE);
      assert_eq!(Posit::<10, 3, i16>::round_from(f64::MIN_POSITIVE), Posit::<10, 3, i16>::MIN_POSITIVE);
    }

    #[test]
    fn max_negative() {
      assert_eq!(crate::p8::round_from(-f64::MIN_POSITIVE), crate::p8::MAX_NEGATIVE);
      assert_eq!(crate::p16::round_from(-f64::MIN_POSITIVE), crate::p16::MAX_NEGATIVE);
      assert_eq!(crate::p32::round_from(-f64::MIN_POSITIVE), crate::p32::MAX_NEGATIVE);
      assert_eq!(crate::p64::round_from(-f64::MIN_POSITIVE), crate::p64::MAX_NEGATIVE);
      assert_eq!(Posit::<8, 0, i8>::round_from(-f64::MIN_POSITIVE), Posit::<8, 0, i8>::MAX_NEGATIVE);
      assert_eq!(Posit::<10, 0, i16>::round_from(-f64::MIN_POSITIVE), Posit::<10, 0, i16>::MAX_NEGATIVE);
      assert_eq!(Posit::<10, 1, i16>::round_from(-f64::MIN_POSITIVE), Posit::<10, 1, i16>::MAX_NEGATIVE);
      assert_eq!(Posit::<10, 2, i16>::round_from(-f64::MIN_POSITIVE), Posit::<10, 2, i16>::MAX_NEGATIVE);
      assert_eq!(Posit::<10, 3, i16>::round_from(-f64::MIN_POSITIVE), Posit::<10, 3, i16>::MAX_NEGATIVE);
    }

    const PROPTEST_CASES: u32 = if cfg!(debug_assertions) {0x1_0000} else {0x80_0000};
    proptest!{
      #![proptest_config(ProptestConfig::with_cases(PROPTEST_CASES))]

      #[test]
      fn posit_10_0_proptest(float in any::<f64>()) {
        assert!(is_correct_rounded::<10, 0, i16>(float), "{:?}", float)
      }

      #[test]
      fn posit_10_1_proptest(float in any::<f64>()) {
        assert!(is_correct_rounded::<10, 1, i16>(float), "{:?}", float)
      }

      #[test]
      fn posit_10_2_proptest(float in any::<f64>()) {
        assert!(is_correct_rounded::<10, 2, i16>(float), "{:?}", float)
      }

      #[test]
      fn posit_10_3_proptest(float in any::<f64>()) {
        assert!(is_correct_rounded::<10, 3, i16>(float), "{:?}", float)
      }

      #[test]
      fn posit_8_0_proptest(float in any::<f64>()) {
        assert!(is_correct_rounded::<8, 0, i8>(float), "{:?}", float)
      }

      #[test]
      fn p8_proptest(float in any::<f64>()) {
        assert!(is_correct_rounded::<8, 2, i8>(float), "{:?}", float)
      }

      #[test]
      fn p16_proptest(float in any::<f64>()) {
        assert!(is_correct_rounded::<16, 2, i16>(float), "{:?}", float)
      }

      #[test]
      fn p32_proptest(float in any::<f64>()) {
        assert!(is_correct_rounded::<32, 2, i32>(float), "{:?}", float)
      }

      #[test]
      fn p64_proptest(float in any::<f64>()) {
        assert!(is_correct_rounded::<64, 2, i64>(float), "{:?}", float)
      }
    }
  }

  mod f32 {
    use super::*;

    /// Aux function: check that `float` is converted to a posit with the correct rounding.
    fn is_correct_rounded<const N: u32, const ES: u32, Int: crate::Int>(float: f32) -> bool
    where
      Rational: From<Decoded<N, ES, Int>> + TryFrom<Posit<N, ES, Int>> + TryFrom<f32>,
      <Rational as TryFrom<Posit<N, ES, Int>>>::Error: core::fmt::Debug
    {
      let posit = Posit::<N, ES, Int>::round_from(float);
      match Rational::try_from(float) {
        Ok(exact) => super::rational::is_correct_rounded(exact, posit),
        Err(_) => posit == Posit::NAR,
      }
    }

    #[test]
    fn zero() {
      assert_eq!(crate::p8::round_from(0.0f32), crate::p8::ZERO);
      assert_eq!(crate::p16::round_from(0.0f32), crate::p16::ZERO);
      assert_eq!(crate::p32::round_from(0.0f32), crate::p32::ZERO);
      assert_eq!(crate::p64::round_from(0.0f32), crate::p64::ZERO);
      assert_eq!(Posit::<8, 0, i8>::round_from(0.0f32), Posit::<8, 0, i8>::ZERO);
      assert_eq!(Posit::<10, 0, i16>::round_from(0.0f32), Posit::<10, 0, i16>::ZERO);
      assert_eq!(Posit::<10, 1, i16>::round_from(0.0f32), Posit::<10, 1, i16>::ZERO);
      assert_eq!(Posit::<10, 2, i16>::round_from(0.0f32), Posit::<10, 2, i16>::ZERO);
      assert_eq!(Posit::<10, 3, i16>::round_from(0.0f32), Posit::<10, 3, i16>::ZERO);
    }

    #[test]
    fn one() {
      assert_eq!(crate::p8::round_from(1.0f32), crate::p8::ONE);
      assert_eq!(crate::p16::round_from(1.0f32), crate::p16::ONE);
      assert_eq!(crate::p32::round_from(1.0f32), crate::p32::ONE);
      assert_eq!(crate::p64::round_from(1.0f32), crate::p64::ONE);
      assert_eq!(Posit::<8, 0, i8>::round_from(1.0f32), Posit::<8, 0, i8>::ONE);
      assert_eq!(Posit::<10, 0, i16>::round_from(1.0f32), Posit::<10, 0, i16>::ONE);
      assert_eq!(Posit::<10, 1, i16>::round_from(1.0f32), Posit::<10, 1, i16>::ONE);
      assert_eq!(Posit::<10, 2, i16>::round_from(1.0f32), Posit::<10, 2, i16>::ONE);
      assert_eq!(Posit::<10, 3, i16>::round_from(1.0f32), Posit::<10, 3, i16>::ONE);
    }

    #[test]
    fn minus_one() {
      assert_eq!(crate::p8::round_from(-1.0f32), crate::p8::MINUS_ONE);
      assert_eq!(crate::p16::round_from(-1.0f32), crate::p16::MINUS_ONE);
      assert_eq!(crate::p32::round_from(-1.0f32), crate::p32::MINUS_ONE);
      assert_eq!(crate::p64::round_from(-1.0f32), crate::p64::MINUS_ONE);
      assert_eq!(Posit::<8, 0, i8>::round_from(-1.0f32), Posit::<8, 0, i8>::MINUS_ONE);
      assert_eq!(Posit::<10, 0, i16>::round_from(-1.0f32), Posit::<10, 0, i16>::MINUS_ONE);
      assert_eq!(Posit::<10, 1, i16>::round_from(-1.0f32), Posit::<10, 1, i16>::MINUS_ONE);
      assert_eq!(Posit::<10, 2, i16>::round_from(-1.0f32), Posit::<10, 2, i16>::MINUS_ONE);
      assert_eq!(Posit::<10, 3, i16>::round_from(-1.0f32), Posit::<10, 3, i16>::MINUS_ONE);
    }

    #[test]
    fn nan() {
      assert_eq!(crate::p8::round_from(f32::NAN), crate::p8::NAR);
      assert_eq!(crate::p16::round_from(f32::NAN), crate::p16::NAR);
      assert_eq!(crate::p32::round_from(f32::NAN), crate::p32::NAR);
      assert_eq!(crate::p64::round_from(f32::NAN), crate::p64::NAR);
      assert_eq!(Posit::<8, 0, i8>::round_from(f32::NAN), Posit::<8, 0, i8>::NAR);
      assert_eq!(Posit::<10, 0, i16>::round_from(f32::NAN), Posit::<10, 0, i16>::NAR);
      assert_eq!(Posit::<10, 1, i16>::round_from(f32::NAN), Posit::<10, 1, i16>::NAR);
      assert_eq!(Posit::<10, 2, i16>::round_from(f32::NAN), Posit::<10, 2, i16>::NAR);
      assert_eq!(Posit::<10, 3, i16>::round_from(f32::NAN), Posit::<10, 3, i16>::NAR);
    }

    #[test]
    fn min_positive() {
      assert_eq!(crate::p8::round_from(f32::MIN_POSITIVE), crate::p8::MIN_POSITIVE);
      assert_eq!(crate::p16::round_from(f32::MIN_POSITIVE), crate::p16::MIN_POSITIVE);
      assert_eq!(crate::p32::round_from(f32::MIN_POSITIVE), crate::p32::MIN_POSITIVE);
      // assert_eq!(crate::p64::round_from(f32::MIN_POSITIVE), crate::p64::MIN_POSITIVE);
      assert_eq!(Posit::<8, 0, i8>::round_from(f32::MIN_POSITIVE), Posit::<8, 0, i8>::MIN_POSITIVE);
      assert_eq!(Posit::<10, 0, i16>::round_from(f32::MIN_POSITIVE), Posit::<10, 0, i16>::MIN_POSITIVE);
      assert_eq!(Posit::<10, 1, i16>::round_from(f32::MIN_POSITIVE), Posit::<10, 1, i16>::MIN_POSITIVE);
      assert_eq!(Posit::<10, 2, i16>::round_from(f32::MIN_POSITIVE), Posit::<10, 2, i16>::MIN_POSITIVE);
      assert_eq!(Posit::<10, 3, i16>::round_from(f32::MIN_POSITIVE), Posit::<10, 3, i16>::MIN_POSITIVE);
    }

    #[test]
    fn max_negative() {
      assert_eq!(crate::p8::round_from(-f32::MIN_POSITIVE), crate::p8::MAX_NEGATIVE);
      assert_eq!(crate::p16::round_from(-f32::MIN_POSITIVE), crate::p16::MAX_NEGATIVE);
      assert_eq!(crate::p32::round_from(-f32::MIN_POSITIVE), crate::p32::MAX_NEGATIVE);
      // assert_eq!(crate::p64::round_from(-f32::MIN_POSITIVE), crate::p64::MAX_NEGATIVE);
      assert_eq!(Posit::<8, 0, i8>::round_from(-f32::MIN_POSITIVE), Posit::<8, 0, i8>::MAX_NEGATIVE);
      assert_eq!(Posit::<10, 0, i16>::round_from(-f32::MIN_POSITIVE), Posit::<10, 0, i16>::MAX_NEGATIVE);
      assert_eq!(Posit::<10, 1, i16>::round_from(-f32::MIN_POSITIVE), Posit::<10, 1, i16>::MAX_NEGATIVE);
      assert_eq!(Posit::<10, 2, i16>::round_from(-f32::MIN_POSITIVE), Posit::<10, 2, i16>::MAX_NEGATIVE);
      assert_eq!(Posit::<10, 3, i16>::round_from(-f32::MIN_POSITIVE), Posit::<10, 3, i16>::MAX_NEGATIVE);
    }

    const PROPTEST_CASES: u32 = if cfg!(debug_assertions) {0x1_0000} else {0x80_0000};
    proptest!{
      #![proptest_config(ProptestConfig::with_cases(PROPTEST_CASES))]

      #[test]
      fn posit_10_0_proptest(float in any::<f32>()) {
        assert!(is_correct_rounded::<10, 0, i16>(float), "{:?}", float)
      }

      #[test]
      fn posit_10_1_proptest(float in any::<f32>()) {
        assert!(is_correct_rounded::<10, 1, i16>(float), "{:?}", float)
      }

      #[test]
      fn posit_10_2_proptest(float in any::<f32>()) {
        assert!(is_correct_rounded::<10, 2, i16>(float), "{:?}", float)
      }

      #[test]
      fn posit_10_3_proptest(float in any::<f32>()) {
        assert!(is_correct_rounded::<10, 3, i16>(float), "{:?}", float)
      }

      #[test]
      fn posit_8_0_proptest(float in any::<f32>()) {
        assert!(is_correct_rounded::<8, 0, i8>(float), "{:?}", float)
      }

      #[test]
      fn p8_proptest(float in any::<f32>()) {
        assert!(is_correct_rounded::<8, 2, i8>(float), "{:?}", float)
      }

      #[test]
      fn p16_proptest(float in any::<f32>()) {
        assert!(is_correct_rounded::<16, 2, i16>(float), "{:?}", float)
      }

      #[test]
      fn p32_proptest(float in any::<f32>()) {
        assert!(is_correct_rounded::<32, 2, i32>(float), "{:?}", float)
      }

      #[test]
      fn p64_proptest(float in any::<f32>()) {
        assert!(is_correct_rounded::<64, 2, i64>(float), "{:?}", float)
      }
    }
  }

  // TODO remove code duplication in tests...?
}
