use super::*;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  /// Return a [normalised](Decoded::is_normalised) `Decoded` that is the result of √x, if `x` is
  /// non-negative.
  ///
  /// # Safety
  ///
  /// `x` must to be [normalised](Decoded::is_normalised) and `x.frac` must be positive, or calling
  /// this function is *undefined behaviour*.
  #[inline]
  pub(crate) unsafe fn sqrt_kernel(x: Decoded<N, ES, Int>) -> (Decoded<N, ES, Int>, Int) {
    // Taking the square root of a number in the form `frac × 2^exp` has two steps.
    //
    // First, ensure that `exp` is an even number. If it's odd, add 1 to exp and compensate `frac`
    // accordingly. That is:
    //
    //   frac', exp' = frac     , exp        if exp is even
    //               = frac << 1, exp - 1    if exp is odd
    //
    // This is fine: `x.frac` is positive, meaning we have exactly 1 bit available to do the shift
    // if we cast to `Int::Unsigned`.
    //
    // Then, the square root is easy.
    //
    //   √(frac' / FRAC_DENOM * 2^exp')
    //   = √(frac') / √(FRAC_DENOM) * 2^(exp' / 2)
    //   = √(frac' * FRAC_DENOM) / FRAC_DENOM * 2^(exp' / 2)
    //
    // In other words: the resulting `exp` is `exp >> 1` (not forgetting to accumulate this lost
    // bit onto `sticky`), and the `frac` is the integer square root of `frac << FRAC_WIDTH`.

    use crate::underlying::Unsigned;
    let exp_odd = x.exp & Int::ONE;

    let frac_adjusted = (x.frac).as_unsigned() << exp_odd.as_u32();
    let exp_adjusted = x.exp - exp_odd;

    let result = frac_adjusted.shift_sqrt(Decoded::<N, ES, Int>::FRAC_WIDTH);
    let frac = Int::of_unsigned(result.0);
    let exp = exp_adjusted >> 1;
    let sticky = Int::from(result.1) | (exp_adjusted & Int::ONE);

    (Decoded{frac, exp}, sticky)
  }

  /// Returns the square root of `self`, rounded. If `self` is negative or [NaR](Self::NAR),
  /// returns NaR.
  ///
  /// Standard: "[**sqrt**](https://posithub.org/docs/posit_standard-2.pdf#subsection.5.5)".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// # use core::f64::consts::PI;
  /// assert_eq!(p16::sqrt((4. * PI).round_into()), p16::round_from(3.5449));
  /// assert_eq!(p16::MINUS_ONE.sqrt(), p16::NAR);
  /// ```
  pub fn sqrt(self) -> Self {
    if self < Self::ZERO {
      Self::NAR
    } else if self == Self::ZERO {
      Self::ZERO
    } else {
      // SAFETY: `self` is not 0 or NaR
      let x = unsafe { self.decode_regular() };
      // SAFETY: `self` is non-negative
      let (result, sticky) = unsafe { Self::sqrt_kernel(x) };
      // SAFETY: `result.is_normalised()` holds
      unsafe { result.encode_regular_round(sticky) }
    }
  }
}

#[cfg(test)]
mod tests {
  use crate::Posit;
  use malachite::{rational::Rational, Natural};
  use proptest::prelude::*;

  /// Aux function: check that `x.sqrt()` is rounded correctly.
  fn is_correct_rounded<const N: u32, const ES: u32, Int: crate::Int>(
    x: Posit<N, ES, Int>,
  ) -> bool
  where
    Rational: TryFrom<Posit<N, ES, Int>, Error = super::rational::IsNaR>, 
  {
    let posit = x.sqrt();
    if let Ok(rational) = Rational::try_from(x)
    && rational >= Rational::from(0) {
      use malachite::base::num::arithmetic::traits::{PowerOf2, FloorSqrt};
      let factor =  Rational::power_of_2((N as u64) << ES << 1);
      let natural = Natural::try_from(rational * &factor * &factor).unwrap();
      let exact = Rational::from_naturals(natural.floor_sqrt(), factor.into_numerator());
      super::rational::is_correct_rounded(exact, posit)
    } else {
      posit == Posit::NAR
    }
  }

  macro_rules! test_exhaustive {
    ($name:ident, $posit:ty) => {
      #[test]
      fn $name() {
        for p in <$posit>::cases_exhaustive_all() {
          assert!(is_correct_rounded(p), "{p:?}")
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
          assert!(is_correct_rounded(p), "{p:?}")
        }
      }
    };
  }

  test_exhaustive!{posit_10_0_exhaustive, Posit::<10, 0, i16>}
  test_exhaustive!{posit_10_1_exhaustive, Posit::<10, 1, i16>}
  test_exhaustive!{posit_10_2_exhaustive, Posit::<10, 2, i16>}
  test_exhaustive!{posit_10_3_exhaustive, Posit::<10, 3, i16>}

  test_exhaustive!{posit_8_0_exhaustive, Posit::<8, 0, i8>}

  test_exhaustive!{p8_exhaustive, crate::p8}
  test_exhaustive!{p16_exhaustive, crate::p16}
  test_proptest!{p32_proptest, crate::p32}
  test_proptest!{p64_proptest, crate::p64}
  // test_proptest!{p128_proptest, crate::p128}

  test_exhaustive!{posit_3_0_exhaustive, Posit::<3, 0, i8>}
  test_exhaustive!{posit_4_0_exhaustive, Posit::<4, 0, i8>}
  test_exhaustive!{posit_4_1_exhaustive, Posit::<4, 1, i8>}
}
