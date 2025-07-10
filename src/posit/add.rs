use super::*;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  /// `x` and `y` cannot be symmetrical, or calling this function is *undefined behaviour*.
  #[inline]
  pub(crate) unsafe fn add_kernel(x: Decoded<N, ES, Int>, y: Decoded<N, ES, Int>) -> (Decoded<N, ES, Int>, Int) {
    /*dbg!(x, y);*/

    // First, normalise the
    let shift = x.exp - y.exp;
    let (x, y) = if shift.is_positive() { (x, y) } else { (y, x) };
    let shift = shift.abs().as_u32();
    if shift >= Int::BITS {
      return (x, y.frac)
    };
    let xfrac = x.frac;
    let yfrac = y.frac >> shift;
    let exp = x.exp;

    // Adding two positive or two negative values: an overflow by 1 place *must* occur. For example
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
    // To do this we use `overflowing_add_shift`, which may have a specialised implementation
    // using "rotate" instructions; see [crate::underlying].
    let (frac, overflow) = xfrac.overflowing_add_shift(yfrac);
    let exp = exp + overflow.into();

    // Adding a positive and a negative value: an underflow by n places *may* occur. For example
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

    // Now just fix things up so that the rounding is correct. First, in case of underflow by `n`
    // we must recover `n` bits we have shifted out from `yfrac` at the start, and add them to the
    // result. For example, say `y.frac = 0b11110101`, `shift = 4`, `underflow = 3`.
    //
    //    y.frac                        = 0b11110101|
    //    y.frac >> shift               = 0b00001111|0101
    //    y.frac >> (shift - underflow) = 0b01111010|1
    //
    // Second, the sticky bits, which are just the bits of `y.frac` that *were* shifted out
    // and *were not* recovered due to underflow.
    /*dbg!(shift, overflow, underflow, /*true_shift*/);*/
    let true_shift = shift.checked_sub(underflow).unwrap_or(0);
    let recovered = y.frac.mask_lsb(shift) >> true_shift;
    let sticky = y.frac.mask_lsb(true_shift);
    let frac = frac | recovered;

    (Decoded{frac, exp}, sticky)
  }

  pub fn add(self, other: Self) -> Self {
    if self.0 | other.0 == Int::ZERO {
      Self(self.0 | other.0)
    } else if self == Self::NAR || other == Self::NAR {
      Self::NAR
    } else if self.0.wrapping_add(other.0) == Int::ZERO {
      Self(self.0.wrapping_add(other.0))
    } else {
      // SAFETY: neither `self` nor `other` are 0 or NaR; `self` and `other` aren't symmetrical
      unsafe {
        let (result, sticky) = Self::add_kernel(
          self.decode_regular(),
          other.decode_regular(),
        );
        result.encode_regular_round(sticky)
      }
    }
  }
}

impl<const N: u32, const ES: u32, Int: crate::Int>
core::ops::Add<Self> for Posit<N, ES, Int> {
  type Output = Self;
  fn add(self, rhs: Self) -> Self::Output { self.add(rhs) }
}

impl<const N: u32, const ES: u32, Int: crate::Int>
core::ops::Add<&Self> for Posit<N, ES, Int> {
  type Output = Self;
  fn add(self, rhs: &Self) -> Self::Output { self.add(*rhs) }
}

impl<const N: u32, const ES: u32, Int: crate::Int>
core::ops::Add<Posit<N, ES, Int>> for &Posit<N, ES, Int> {
  type Output = Posit<N, ES, Int>;
  fn add(self, rhs: Posit<N, ES, Int>) -> Self::Output { (*self).add(rhs) }
}

impl<const N: u32, const ES: u32, Int: crate::Int>
core::ops::Add<&Posit<N, ES, Int>> for &Posit<N, ES, Int> {
  type Output = Posit<N, ES, Int>;
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
  fn posit_6_0_exhaustive() {
    for a in Posit::<6, 0, i16>::cases_exhaustive() {
      for b in Posit::<6, 0, i16>::cases_exhaustive() {
        assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
      }
    }
  }

  #[test]
  fn posit_6_1_exhaustive() {
    for a in Posit::<6, 1, i16>::cases_exhaustive() {
      for b in Posit::<6, 1, i16>::cases_exhaustive() {
        assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
      }
    }
  }

  #[test]
  fn posit_6_2_exhaustive() {
    for a in Posit::<6, 2, i16>::cases_exhaustive() {
      for b in Posit::<6, 2, i16>::cases_exhaustive() {
        assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
      }
    }
  }

  #[test]
  fn posit_6_3_exhaustive() {
    for a in Posit::<6, 3, i16>::cases_exhaustive() {
      for b in Posit::<6, 3, i16>::cases_exhaustive() {
        assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
      }
    }
  }

  #[test]
  fn p8_exhaustive() {
    for a in crate::p8::cases_exhaustive() {
      for b in crate::p8::cases_exhaustive() {
        assert!(is_correct_rounded(a, b), "{:?}: {:?}", a, b)
      }
    }
  }
}
