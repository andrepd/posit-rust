use super::*;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  #[inline]
  pub(crate) unsafe fn div_kernel(x: Decoded<N, ES, Int>, y: Decoded<N, ES, Int>) -> (Decoded<N, ES, Int>, Int) {
    // Let's use ÷ to denote true mathematical division, and / denote integer division *that rounds
    // down* (i.e. towards negative infinity, not towards zero). To divide two numbers in the form
    // `frac × 2^exp`, we have:
    //
    //   (x.frac ÷ FRAC_DENOM * 2^x.exp) ÷ (y.frac ÷ FRAC_DENOM * 2^y.exp)
    //   = (x.frac ÷ y.frac) * 2^(x.exp - y.exp)
    //   = (x.frac ÷ y.frac * FRAC_DENOM) ÷ FRAC_DENOM * 2^(x.exp - y.exp)
    //
    // Since we know `FRAC_DENOM` = `2^FRAC_WIDTH`, we can re-arrange the expression one more
    // time:
    //
    //   = (x.frac ÷ y.frac * 2^FRAC_WIDTH) ÷ FRAC_DENOM * 2^(x.exp - y.exp)
    //   = ((x.frac ÷ y.frac) << FRAC_WIDTH) ÷ FRAC_DENOM * 2^(x.exp - y.exp)
    //   = ((x.frac << FRAC_WIDTH) / y.frac) ÷ FRAC_DENOM * 2^(x.exp - y.exp)
    //
    // Meaning the result has
    //
    //   frac = (x.frac << FRAC_WIDTH) / y.frac
    //    exp = x.exp - y.exp
    //
    // But this is not quite correct. This is because `(x.frac << FRAC_WIDTH) / y.frac` may
    // underflow, which means some bits will be lost at the end. To avoid this, we compute the
    // `underflow` first, then adjust the shift amount and the exponent accordingly.
    //
    //   frac = (x.frac << (FRAC_WIDTH + underflow)) / y.frac
    //    exp = x.exp - y.exp - underflow

    // TODO: The current implementation does two divisions, which is expensive. But the `underflow`
    // can really only be [0,1,2]. Maybe we can determine this by just looking at the signs and
    // relative magnitudes of the `frac`s, without dividing. Then we only need to do the second
    // division.
    let (div, _) = x.frac.shift_div_rem(y.frac, Decoded::<N, ES, Int>::FRAC_WIDTH);
    // SAFETY: `x.frac` and `y.frac` are not 0, so `div` cannot be 0; nor can it ever be MIN
    let underflow = unsafe { div.leading_run_minus_one() };

    let (frac, sticky) = x.frac.shift_div_rem(y.frac, Decoded::<N, ES, Int>::FRAC_WIDTH + underflow);
    let exp = x.exp - y.exp - Int::of_u32(underflow);

    (Decoded{frac, exp}, sticky)
  }

  pub(crate) fn div(self, other: Self) -> Self {
    if self == Self::NAR || other == Self::NAR || other == Self::ZERO {
      Self::NAR
    } else if self == Self::ZERO {
      Self::ZERO
    } else {
      // SAFETY: neither `self` nor `other` are 0 or NaR
      let a = unsafe { self.decode_regular() };
      let b = unsafe { other.decode_regular() };
      let (result, sticky) = unsafe { Self::div_kernel(a, b) };
      // SAFETY: `result` does not have an underflowing `frac`
      unsafe { result.encode_regular_round(sticky) }
    }
  }
}

use core::ops::{Div, DivAssign};

super::mk_ops!{Div, DivAssign, div, div_assign}

#[cfg(test)]
mod tests {
  use super::*;
  use malachite::rational::Rational;

  #[allow(dead_code)]
  fn ops() {
    let mut a = crate::p32::ONE;
    let mut b = crate::p32::MINUS_ONE;
    let _ = a / b;
    let _ = &a / b;
    let _ = a / &b;
    let _ = &a / &b;
    a /= b;
    b /= &a;
  }

  /// Aux function: check that `a / b` is rounded correctly.
  fn is_correct_rounded<const N: u32, const ES: u32, Int: crate::Int>(
    a: Posit<N, ES, Int>,
    b: Posit<N, ES, Int>,
  ) -> bool
  where
    Rational: TryFrom<Posit<N, ES, Int>>,
    <Rational as TryFrom<Posit<N, ES, Int>>>::Error: core::fmt::Debug
  {
    let mul_posit = a / b;
    if let (Ok(a), Ok(b)) = (Rational::try_from(a), Rational::try_from(b))
    && b != Rational::from(0) {
      let mul_exact = a / b;
      super::rational::is_correct_rounded(mul_exact, mul_posit)
    } else {
      mul_posit == Posit::<N, ES, Int>::NAR
    }
  }

  // TODO Factor all these into a macro

  #[test]
  fn posit_10_0_exhaustive() {
    for a in Posit::<10, 0, i16>::cases_exhaustive_all() {
      for b in Posit::<10, 0, i16>::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?} / {:?}", a, b)
      }
    }
  }

  #[test]
  fn posit_10_1_exhaustive() {
    for a in Posit::<10, 1, i16>::cases_exhaustive_all() {
      for b in Posit::<10, 1, i16>::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?} / {:?}", a, b)
      }
    }
  }

  #[test]
  fn posit_10_2_exhaustive() {
    for a in Posit::<10, 2, i16>::cases_exhaustive_all() {
      for b in Posit::<10, 2, i16>::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?} / {:?}", a, b)
      }
    }
  }

  #[test]
  fn posit_10_3_exhaustive() {
    for a in Posit::<10, 3, i16>::cases_exhaustive_all() {
      for b in Posit::<10, 3, i16>::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?} / {:?}", a, b)
      }
    }
  }

  #[test]
  fn posit_8_0_exhaustive() {
    for a in Posit::<8, 0, i8>::cases_exhaustive_all() {
      for b in Posit::<8, 0, i8>::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?} / {:?}", a, b)
      }
    }
  }

  #[test]
  fn p8_exhaustive() {
    for a in crate::p8::cases_exhaustive_all() {
      for b in crate::p8::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?} / {:?}", a, b)
      }
    }
  }

  use proptest::prelude::*;
  proptest!{
    #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]

    #[test]
    fn p16_proptest(
      a in crate::p16::cases_proptest(),
      b in crate::p16::cases_proptest(),
    ) {
      assert!(is_correct_rounded(a, b), "{:?} / {:?}", a, b)
    }

    #[test]
    fn p32_proptest(
      a in crate::p32::cases_proptest(),
      b in crate::p32::cases_proptest(),
    ) {
      assert!(is_correct_rounded(a, b), "{:?} / {:?}", a, b)
    }

    #[test]
    fn p64_proptest(
      a in crate::p64::cases_proptest(),
      b in crate::p64::cases_proptest(),
    ) {
      assert!(is_correct_rounded(a, b), "{:?} / {:?}", a, b)
    }
  }

  #[test]
  fn posit_3_0_exhaustive() {
    for a in Posit::<3, 0, i8>::cases_exhaustive_all() {
      for b in Posit::<3, 0, i8>::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?} / {:?}", a, b)
      }
    }
  }
  #[test]
  fn posit_4_0_exhaustive() {
    for a in Posit::<4, 0, i8>::cases_exhaustive_all() {
      for b in Posit::<4, 0, i8>::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?} / {:?}", a, b)
      }
    }
  }
  #[test]
  fn posit_4_1_exhaustive() {
    for a in Posit::<4, 1, i8>::cases_exhaustive_all() {
      for b in Posit::<4, 1, i8>::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?} / {:?}", a, b)
      }
    }
  }
}
