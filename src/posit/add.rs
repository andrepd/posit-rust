use super::*;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  /// `x` and `y` cannot be symmetrical, or calling this function is *undefined behaviour*.
  #[inline]
  pub(crate) unsafe fn add_kernel(x: Decoded<N, ES, Int>, y: Decoded<N, ES, Int>) -> (Decoded<N, ES, Int>, Int) {
    // Adding two numbers in the form `x.frac × 2^x.exp` and `y.exp × 2^y.exp` is easy, if only
    // `x.exp` = `y.exp`: then the result would be just `(x.frac + y.exp) × 2^x.exp`. Therefore,
    // to add two numbers we just have to (1) reduce to the same exponent, and (2) add the
    // fractions. The remaining complications are to do with detecting over/underflows, and
    // rounding correctly.

    // First align the exponents. That is: to add `x.frac + 2^x.exp` and `y.frac + 2^y.exp` let
    // `shift` be the difference between the exponents, add `shift` to the smallest exp, and
    // divide the corresponding frac by `2^shift` to compensate. For example:
    //
    //     0b01_0110 × 2⁰
    //   + 0b01_1000 × 2³
    //
    // becomes
    //
    //     0b00_0010110 × 2³
    //   + 0b01_1000    × 2³
    //
    // because the first number has the smallest `exp`, so we add 3 to it and divide its `frac` by
    // 2³.
    let shift = x.exp - y.exp;
    let (x, y) = if shift.is_positive() { (x, y) } else { (y, x) };
    let shift = shift.abs().as_u32();
    // One thing to keep in mind is that `shift` can exceed the width of `Int`. If this happens,
    // then the *entire* contents of `y.frac` are shifted out, and thus the answer is just `x`.
    if shift >= Int::BITS {  // TODO mark unlikely?
      return (x, Int::ZERO)
    };
    let xfrac = x.frac;
    let yfrac = y.frac >> shift;
    let exp = x.exp;

    // Adding two positive or two negative values: an overflow by *1 place* may occur. For example
    //
    //     1.25 = 0b01_0100
    //   + 1.0  = 0b01_0000
    //   = 2.25 = 0b10_0100
    //
    // If this happens, we must detect this, shift the `frac` right by 1 (i.e. divide by 2), and
    // add 1 to exponent to compensate
    //
    //   = 1.125 × 2¹ = 0b01_0010, add +1 to `exp`
    //
    // To do this we use `overflowing_add_shift`, which may have a specialised implementation e.g.
    // using "rotate" instructions; see [crate::underlying].
    let (frac, overflow) = xfrac.overflowing_add_shift(yfrac);
    let exp = exp + overflow.into();
    // If an overflow occurs, then remember to also accumulate the shifted out bit of xfrac and
    // yfrac into sticky.
    let sticky_overflow = (xfrac | yfrac) & overflow.into();

    // Adding a positive and a negative value: an underflow by *n places* may occur. For example
    //
    //     -1.25 = 0b10_1100
    //   +  1.0  = 0b01_0000
    //   = -0.25 = 0b11_1100
    //
    // If this happens, we must detect this, shift the `frac` left by `n` (i.e. multiply by 2^n),
    // and subtract `n` to the exponent to compensate.
    //
    //   = -1.00 × 2¯³ = 0b10_0000
    //
    // To do this we use our trusty `leading_run_minus_one`, since we want to detect that the
    // number starts with n 0s followed by a 1 or n 1s followed by a 0, and shift them so that
    // it's just a 01 or a 10.
    // SAFETY: x and y are not symmetrical (precondition), so `frac` cannot be 0
    let underflow = unsafe { frac.leading_run_minus_one() };
    let frac = frac << underflow as u32;
    let exp = exp - Int::of_u32(underflow);
    // If an underflow by `n` occurs, then we need to "recover" `n` of the bits we have shifted out
    // in `yfrac`, and add them onto the result, because we have set `yfrac = y.frac >> shift`,
    // but actually should have set `= y.frac >> (shift - underflow)`.
    //
    // For example, say `y.frac = 0b11110101`, `shift = 4`, `underflow = 3`. Then
    //
    //    y.frac                        = 0b11110101|
    //    y.frac >> shift               = 0b00001111|0101    ← discarded 4 bits
    //    y.frac >> (shift - underflow) = 0b01111010|1       ← but should only discard 1
    //
    // Here only 1 bit should be shifted out to sticky.
    let true_shift = shift.checked_sub(underflow).unwrap_or(0);  // TODO ver
    let recovered = y.frac.mask_lsb(shift) >> true_shift;
    let sticky = y.frac.mask_lsb(true_shift);
    let frac = frac | recovered;

    (Decoded{frac, exp}, (sticky | sticky_overflow))
  }

  pub(crate) fn add(self, other: Self) -> Self {
    let sum = self.0.wrapping_add(other.0);
    if self == Self::NAR || other == Self::NAR {
      Self::NAR
    } else if sum == Int::ZERO || sum == self.0 || sum == other.0 {
      Self(sum)
    } else {
      // SAFETY: neither `self` nor `other` are 0 or NaR.
      let a = unsafe { self.decode_regular() };
      let b = unsafe { other.decode_regular() };
      // SAFETY: `self` and `other` aren't symmetrical
      let (result, sticky) = unsafe { Self::add_kernel(a, b) };
      // SAFETY: `result` does not have an underflowing `frac`.
      unsafe { result.encode_regular_round(sticky) }
    }
  }
}

impl<const N: u32, const ES: u32, Int: crate::Int>
core::ops::Add<Self> for Posit<N, ES, Int> {
  type Output = Self;
  #[inline]
  fn add(self, rhs: Self) -> Self::Output { self.add(rhs) }
}

impl<const N: u32, const ES: u32, Int: crate::Int>
core::ops::Add<&Self> for Posit<N, ES, Int> {
  type Output = Self;
  #[inline]
  fn add(self, rhs: &Self) -> Self::Output { self.add(*rhs) }
}

impl<const N: u32, const ES: u32, Int: crate::Int>
core::ops::Add<Posit<N, ES, Int>> for &Posit<N, ES, Int> {
  type Output = Posit<N, ES, Int>;
  #[inline]
  fn add(self, rhs: Posit<N, ES, Int>) -> Self::Output { (*self).add(rhs) }
}

impl<const N: u32, const ES: u32, Int: crate::Int>
core::ops::Add<&Posit<N, ES, Int>> for &Posit<N, ES, Int> {
  type Output = Posit<N, ES, Int>;
  #[inline]
  fn add(self, rhs: &Posit<N, ES, Int>) -> Self::Output { (*self).add(*rhs) }
}

#[cfg(test)]
mod tests {
  use super::*;
  use malachite::rational::Rational;

  /// Aux function: check that `a + b` is rounded correctly.
  fn is_correct_rounded<const N: u32, const ES: u32, Int: crate::Int>(
    a: Posit<N, ES, Int>,
    b: Posit<N, ES, Int>,
  ) -> bool
  where
    Rational: TryFrom<Posit<N, ES, Int>>,
    <Rational as TryFrom<Posit<N, ES, Int>>>::Error: core::fmt::Debug
  {
    let sum_posit = a + b;
    if let (Ok(a), Ok(b)) = (Rational::try_from(a), Rational::try_from(b)) {
      let sum_exact = a + b;
      super::rational::is_correct_rounded(sum_exact, sum_posit)
    } else {
      sum_posit == Posit::<N, ES, Int>::NAR
    }
  }

  #[test]
  fn posit_10_0_exhaustive() {
    for a in Posit::<10, 0, i16>::cases_exhaustive_all() {
      for b in Posit::<10, 0, i16>::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
      }
    }
  }

  #[test]
  fn posit_10_1_exhaustive() {
    for a in Posit::<10, 1, i16>::cases_exhaustive_all() {
      for b in Posit::<10, 1, i16>::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
      }
    }
  }

  #[test]
  fn posit_10_2_exhaustive() {
    for a in Posit::<10, 2, i16>::cases_exhaustive_all() {
      for b in Posit::<10, 2, i16>::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
      }
    }
  }

  #[test]
  fn posit_10_3_exhaustive() {
    for a in Posit::<10, 3, i16>::cases_exhaustive_all() {
      for b in Posit::<10, 3, i16>::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
      }
    }
  }

  #[test]
  fn p8_exhaustive() {
    for a in crate::p8::cases_exhaustive_all() {
      for b in crate::p8::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
      }
    }
  }

  #[test]
  fn posit_8_0_exhaustive() {
    for a in Posit::<8, 0, i8>::cases_exhaustive_all() {
      for b in Posit::<8, 0, i8>::cases_exhaustive_all() {
        assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
      }
    }
  }

  use proptest::prelude::*;
  const PROPTEST_CASES: u32 = if cfg!(debug_assertions) {0x1_0000} else {0x80_0000};
  proptest!{
    #![proptest_config(ProptestConfig::with_cases(PROPTEST_CASES))]

    #[test]
    fn p16_proptest(
      a in crate::p16::cases_proptest(),
      b in crate::p16::cases_proptest(),
    ) {
      assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
    }

    #[test]
    fn p32_proptest(
      a in crate::p32::cases_proptest(),
      b in crate::p32::cases_proptest(),
    ) {
      assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
    }

    #[test]
    fn p64_proptest(
      a in crate::p64::cases_proptest(),
      b in crate::p64::cases_proptest(),
    ) {
      assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
    }
  }
}
