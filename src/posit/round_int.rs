use super::*;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  // TODO note that these functions can probably be made more efficient if we don't call
  // encode/decode, since all we have to do is manipulate the `frac` field without touching the
  // exponents (not quite, because of overflow, but that overflow of frac into exp and regime is
  // handled elegantly due to the posit bit format).

  /// Returns the integer-valued posit nearest to `self`, and the nearest even integer-valued posit
  /// if two integers are equally near.
  ///
  /// Standard: "[**nearestInt**](https://posithub.org/docs/posit_standard-2.pdf#subsection.5.2)".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(p32::round_from(3.1).nearest_int(), p32::round_from(3));
  /// assert_eq!(p32::round_from(3.5).nearest_int(), p32::round_from(4));
  /// assert_eq!(p32::round_from(3.9).nearest_int(), p32::round_from(4));
  /// ```
  pub fn nearest_int(self) -> Self {
    if self.is_special() { return self }
    // SAFETY: `self` is not 0 or NaR
    let decoded = unsafe { self.decode_regular() };

    // Let's split `decoded.frac` into an `integral` (left of the decimal dot) and `fractional`
    // (right of the decimal dot) part. For an `exp` of 0, the decimal dot is `FRAC_WIDTH` places
    // from the right / 2 places from the left. If the `exp` is bigger or smaller, the dot moves
    // right or left respectively.
    //
    // Examples:
    //
    //         frac: 0b01_1101
    //          exp: +0
    //     integral: 0b01
    //   fractional: 0b110100
    //
    //         frac: 0b01_1101
    //          exp: +2
    //     integral: 0b0111
    //   fractional: 0b010000
    //
    //         frac: 0b01_1101
    //          exp: -1
    //     integral: 0b0
    //   fractional: 0b101110
    let integral_bits = (Int::ONE + Int::ONE).wrapping_add(decoded.exp);

    // If there are no bits in the integral part, then the result is just 0.
    //
    //   - Positive case: 0b01_xxxx ×2^-2 = [+0.25,+0.50[ ⇒ rounds to 0
    //   - Negative case: 0b10_xxxx ×2^-2 = [-0.50,-0.25[ ⇒ rounds to 0
    if integral_bits <= Int::ZERO {
      return Posit::ZERO
    }
    // If the are no bits in the fractional part, then the result is the posit itself, which is
    // already an integer.
    if integral_bits >= Int::of_u32(Int::BITS) {
      return self;
    }

    // Otherwise, grab the integral and fractional part. The fractional part tells us whether we
    // need to round the integral part up or not: we do round up if the fractional part is greater
    // than 0.5, or if it is exactly 0.5 and the integral part is odd (so that we round to an even
    // number).
    let integral_bits = integral_bits.as_u32();
    let fractional_bits = Int::BITS - integral_bits;
    let integral = decoded.frac >> fractional_bits;
    let fractional = decoded.frac << integral_bits;

    // If `fractional` is `0b0xxx…`, then we round down. If it's `0b1xxx…`, then we round up,
    // unless it's exactly `0b1000…`, in which case we round up if `integral` is odd.
    let round = !fractional.is_positive();
    let sticky = fractional << 1 != Int::ZERO;
    let odd = integral.get_lsb();
    let round_up: bool = round & (odd | sticky);

    // TODO This is an interesting alternative formulation of the round_up formula, maybe we can
    // use it elsewhere too.
    /*let round_up = !(fractional | Int::from(odd)).is_positive();*/

    // Tricky detail! If we do round up, we might overflow to the next exponent (e.g. from 0b01_11
    // to 0b01_000); if this happens then we must subtract 1 from `fractional_bits` and add 1 to
    // `exp`. In the case of a negative `frac`, the reverse might happen. To handle both cases
    // without branching, we turn to our trusty `leading_run_minus_one`.
    let integral_rounded = integral + Int::from(round_up);
    if integral_rounded == Int::ZERO {
      return Posit::ZERO
    }
    // SAFETY: `integral_rounded` is not 0 (checked) nor Int::MIN (impossible)
    let true_fractional_bits = unsafe { integral_rounded.leading_run_minus_one() };
    let frac = integral_rounded << true_fractional_bits;
    let exp = decoded.exp + (Int::of_u32(fractional_bits) - Int::of_u32(true_fractional_bits));

    // SAFETY: `frac` can only be underflowing if it's 0, which we checked above.
    unsafe { Decoded { frac, exp }.encode_regular() }
  }

  /// Returns the largest integer-valued posit less than or equal to `self`.
  ///
  /// Standard: "[**floor**](https://posithub.org/docs/posit_standard-2.pdf#subsection.5.2)".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(p32::round_from(3.1).floor(), p32::round_from(3));
  /// assert_eq!(p32::round_from(3.5).floor(), p32::round_from(3));
  /// assert_eq!(p32::round_from(3.9).floor(), p32::round_from(3));
  /// ```
  pub fn floor(self) -> Self {
    // `floor` follows the same template as `nearest_int`, only it is considerably simpler because
    // we don't care about rounding. For details, see the comments in the code of [`nearest_int`].

    if self.is_special() { return self }
    // SAFETY: `self` is not 0 or NaR
    let decoded = unsafe { self.decode_regular() };

    let integral_bits = (Int::ONE + Int::ONE).wrapping_add(decoded.exp);

    // If there are no bits in the integral part, then the result is 0 or -1.
    //
    //   - Positive case: 0b01_xxxx ×2^-2 = [+0.25,+0.50[ ⇒ rounds to 0
    //   - Negative case: 0b10_xxxx ×2^-2 = [-0.50,-0.25[ ⇒ rounds to -1
    if integral_bits <= Int::ZERO {
      return if self >= Posit::ZERO {Posit::ZERO} else {Posit::MINUS_ONE}
    }
    // If the are no bits in the fractional part, then the result is the posit itself, which is
    // already an integer.
    if integral_bits >= Int::of_u32(Int::BITS) {
      return self;
    }

    let integral_bits = integral_bits.as_u32();
    let frac = decoded.frac.mask_msb(integral_bits);
    let exp = decoded.exp;
    if frac == Int::ZERO {
      return Posit::ZERO
    }

    // SAFETY: `frac` can only be underflowing if it's 0, which we checked in the other branch.
    unsafe { Decoded { frac, exp }.encode_regular() }
  }

  /// Returns the smallest integer-valued posit greater than or equal to `self`.
  ///
  /// Standard: "[**ceil**](https://posithub.org/docs/posit_standard-2.pdf#subsection.5.2)".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(p32::round_from(3.1).ceil(), p32::round_from(4));
  /// assert_eq!(p32::round_from(3.5).ceil(), p32::round_from(4));
  /// assert_eq!(p32::round_from(3.9).ceil(), p32::round_from(4));
  /// ```
  pub fn ceil(self) -> Self {
    // `floor` follows the same template as `nearest_int`. Once again we care about rounding, but
    // the rule is considerably simpler: round up if `fractional != 0`. For details, see the
    // comments in the code of [`nearest_int`].

    if self.is_special() { return self }
    // SAFETY: `self` is not 0 or NaR
    let decoded = unsafe { self.decode_regular() };

    let integral_bits = (Int::ONE + Int::ONE).wrapping_add(decoded.exp);
    // If there are no bits in the integral part, then the result is 0 or +1.
    //
    //   - Positive case: 0b01_xxxx ×2^-2 = [+0.25,+0.50[ ⇒ rounds to 1
    //   - Negative case: 0b10_xxxx ×2^-2 = [-0.50,-0.25[ ⇒ rounds to 0
    if integral_bits <= Int::ZERO {
      return if self >= Posit::ZERO {Posit::ONE} else {Posit::ZERO}
    }
    // If the are no bits in the fractional part, then the result is the posit itself, which is
    // already an integer.
    if integral_bits >= Int::of_u32(Int::BITS) {
      return self;
    }

    let integral_bits = integral_bits.as_u32();
    let fractional_bits = Int::BITS - integral_bits;
    let integral = decoded.frac >> fractional_bits;
    let fractional = decoded.frac << integral_bits;

    let round_up: bool = fractional != Int::ZERO;

    let integral_rounded = integral + Int::from(round_up);
    if integral_rounded == Int::ZERO {
      return Posit::ZERO
    }
    // SAFETY: `integral_rounded` is not 0 (checked) nor Int::MIN (impossible)
    let true_fractional_bits = unsafe { integral_rounded.leading_run_minus_one() };
    let frac = integral_rounded << true_fractional_bits;
    let exp = decoded.exp + (Int::of_u32(fractional_bits) - Int::of_u32(true_fractional_bits));

    // SAFETY: `frac` can only be underflowing if it's 0, which we checked in the other branch.
    unsafe { Decoded { frac, exp }.encode_regular() }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use malachite::rational::Rational;
  use proptest::prelude::*;

  use malachite::base::rounding_modes::RoundingMode;

  /// Aux function: check that `posit` rounded to `rounded_posit` is correct for `rounding_mode`.
  fn is_correct_rounded<const N: u32, const ES: u32, Int: crate::Int>(
    posit: Posit<N, ES, Int>,
    rounded_posit: Posit<N, ES, Int>,
    rounding_mode: RoundingMode,
  ) -> bool
  where
    Rational: From<i32> + TryFrom<Posit<N, ES, Int>, Error = super::rational::IsNaR>,
  {
    use malachite::base::num::arithmetic::traits::RoundToMultiple;
    let posit = Rational::try_from(posit)
      .map(|exact| exact.round_to_multiple(Rational::from(1), rounding_mode).0);
    let rounded_posit = Rational::try_from(rounded_posit);
    posit == rounded_posit
  }

  mod nearest_int {
    use super::*;

    macro_rules! test_exhaustive {
      ($name:ident, $posit:ty) => {
        #[test]
        fn $name() {
          for p in <$posit>::cases_exhaustive_all() {
            let rounded = p.nearest_int();
            assert!(is_correct_rounded(p, rounded, RoundingMode::Nearest), "{p:?} {rounded:?}")
          }
        }
      };
    }

    macro_rules! test_proptest {
      ($name:ident, $posit:ty) => {
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
          #[test]
          fn $name(p in <$posit>::cases_proptest_all()) {
            let rounded = p.nearest_int();
            assert!(is_correct_rounded(p, rounded, RoundingMode::Nearest), "{p:?} {rounded:?}")
          }
        }
      };
    }

    test_exhaustive!{posit_10_0_exhaustive, Posit<10, 0, i16>}
    test_exhaustive!{posit_10_1_exhaustive, Posit<10, 1, i16>}
    test_exhaustive!{posit_10_2_exhaustive, Posit<10, 2, i16>}
    test_exhaustive!{posit_10_3_exhaustive, Posit<10, 3, i16>}

    test_exhaustive!{posit_8_0_exhaustive,  Posit<8,  0, i8 >}

    test_exhaustive!{p8_exhaustive, crate::p8}
    test_exhaustive!{p16_exhaustive, crate::p16}
    test_proptest!{p32_proptest, crate::p32}
    test_proptest!{p64_proptest, crate::p64}

    test_exhaustive!{posit_3_0_exhaustive, Posit::<3, 0, i8>}
    test_exhaustive!{posit_4_0_exhaustive, Posit::<4, 0, i8>}
    test_exhaustive!{posit_4_1_exhaustive, Posit::<4, 1, i8>}
  }

  mod floor {
    use super::*;

    macro_rules! test_exhaustive {
      ($name:ident, $posit:ty) => {
        #[test]
        fn $name() {
          for p in <$posit>::cases_exhaustive_all() {
            let rounded = p.floor();
            assert!(is_correct_rounded(p, rounded, RoundingMode::Floor), "{p:?} {rounded:?}")
          }
        }
      };
    }

    macro_rules! test_proptest {
      ($name:ident, $posit:ty) => {
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
          #[test]
          fn $name(p in <$posit>::cases_proptest_all()) {
            let rounded = p.floor();
            assert!(is_correct_rounded(p, rounded, RoundingMode::Floor), "{p:?} {rounded:?}")
          }
        }
      };
    }

    test_exhaustive!{posit_10_0_exhaustive, Posit<10, 0, i16>}
    test_exhaustive!{posit_10_1_exhaustive, Posit<10, 1, i16>}
    test_exhaustive!{posit_10_2_exhaustive, Posit<10, 2, i16>}
    test_exhaustive!{posit_10_3_exhaustive, Posit<10, 3, i16>}

    test_exhaustive!{posit_8_0_exhaustive,  Posit<8,  0, i8 >}

    test_exhaustive!{p8_exhaustive, crate::p8}
    test_exhaustive!{p16_exhaustive, crate::p16}
    test_proptest!{p32_proptest, crate::p32}
    test_proptest!{p64_proptest, crate::p64}

    test_exhaustive!{posit_3_0_exhaustive, Posit::<3, 0, i8>}
    test_exhaustive!{posit_4_0_exhaustive, Posit::<4, 0, i8>}
    test_exhaustive!{posit_4_1_exhaustive, Posit::<4, 1, i8>}
  }

  mod ceil {
    use super::*;

    macro_rules! test_exhaustive {
      ($name:ident, $posit:ty) => {
        #[test]
        fn $name() {
          for p in <$posit>::cases_exhaustive_all() {
            let rounded = p.ceil();
            assert!(is_correct_rounded(p, rounded, RoundingMode::Ceiling), "{p:?} {rounded:?}")
          }
        }
      };
    }

    macro_rules! test_proptest {
      ($name:ident, $posit:ty) => {
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
          #[test]
          fn $name(p in <$posit>::cases_proptest_all()) {
            let rounded = p.ceil();
            assert!(is_correct_rounded(p, rounded, RoundingMode::Ceiling), "{p:?} {rounded:?}")
          }
        }
      };
    }

    test_exhaustive!{posit_10_0_exhaustive, Posit<10, 0, i16>}
    test_exhaustive!{posit_10_1_exhaustive, Posit<10, 1, i16>}
    test_exhaustive!{posit_10_2_exhaustive, Posit<10, 2, i16>}
    test_exhaustive!{posit_10_3_exhaustive, Posit<10, 3, i16>}

    test_exhaustive!{posit_8_0_exhaustive,  Posit<8,  0, i8 >}

    test_exhaustive!{p8_exhaustive, crate::p8}
    test_exhaustive!{p16_exhaustive, crate::p16}
    test_proptest!{p32_proptest, crate::p32}
    test_proptest!{p64_proptest, crate::p64}

    test_exhaustive!{posit_3_0_exhaustive, Posit::<3, 0, i8>}
    test_exhaustive!{posit_4_0_exhaustive, Posit::<4, 0, i8>}
    test_exhaustive!{posit_4_1_exhaustive, Posit::<4, 1, i8>}
  }
}
