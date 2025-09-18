use super::*;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  /// Returns the posit value of the lexicographic successor of `self`'s representation.
  ///
  /// Note that, unlike every other function of a posit, `next` and `prior` do not produce a
  /// [NaR](Posit::NAR) output on a [NaR](Posit::NAR) input.
  ///
  /// Standard: "**next**".
  #[inline]
  pub fn next(self) -> Self {
    Self::from_bits(self.0.wrapping_add(Int::ONE))
  }

  /// Returns the posit value of the lexicographic predecessor of `self`'s representation.
  ///
  /// Note that, unlike every other function of a posit, `next` and `prior` do not produce a
  /// [NaR](Posit::NAR) output on a [NaR](Posit::NAR) input.
  ///
  /// Standard: "**prior**".
  #[inline]
  pub fn prior(self) -> Self {
    Self::from_bits(self.0.wrapping_sub(Int::ONE))
  }
}

impl<const N: u32,const ES: u32,Int: crate::Int>
core::ops::Neg for Posit<N, ES, Int> {
  type Output = Posit<N, ES, Int>;

  /// Standard: "**negate**".
  #[inline]
  fn neg(self) -> Self::Output {
    Posit::from_bits(self.0.wrapping_neg())
  }
}

impl<const N: u32,const ES: u32,Int: crate::Int>
core::ops::Neg for &Posit<N, ES, Int> {
  type Output = Posit<N, ES, Int>;

  /// Standard: "**negate**".
  #[inline]
  fn neg(self) -> Self::Output {
    Posit::from_bits(self.0.wrapping_neg())
  }
}

// TODO make explicit on every documentation whether or not it rounds? Or better to just make
// explicit that `-posit` and `posit.abs()` do not?
//
// TODO And make explicit that NaR inputs are propagated to NaR outputs everywhere? Or just that
// `next` and `prior` do not?

impl<const N: u32,const ES: u32,Int: crate::Int> Posit<N, ES, Int> {
  /// Return the absolute value of `self`.
  ///
  /// Standard: "**abs**".
  #[inline]
  pub fn abs(self) -> Self {
    Posit::from_bits(self.0.wrapping_abs())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use malachite::rational::Rational;

  mod neg {
    use super::*;

    #[test]
    fn p8() {
      assert_eq!(-crate::p8::ZERO, crate::p8::ZERO);
      assert_eq!(-crate::p8::NAR, crate::p8::NAR);
      for p in crate::p8::cases_exhaustive() {
        assert_eq!(Rational::try_from(-p).unwrap(), -Rational::try_from(p).unwrap())
      }
    }

    #[test]
    fn posit_10_1() {
      assert_eq!(-Posit::<10, 0, i16>::ZERO, Posit::<10, 0, i16>::ZERO);
      assert_eq!(-Posit::<10, 0, i16>::NAR, Posit::<10, 0, i16>::NAR);
      for p in Posit::<10, 0, i16>::cases_exhaustive() {
        assert_eq!(Rational::try_from(-p).unwrap(), -Rational::try_from(p).unwrap())
      }
    }
  }

  mod abs {
    use super::*;

    #[test]
    fn p8() {
      use malachite::base::num::arithmetic::traits::Abs;
      assert_eq!(crate::p8::ZERO.abs(), crate::p8::ZERO);
      assert_eq!(crate::p8::NAR.abs(), crate::p8::NAR);
      for p in crate::p8::cases_exhaustive() {
        assert_eq!(Rational::try_from(p.abs()).unwrap(), Rational::try_from(p).unwrap().abs())
      }
    }

    #[test]
    fn posit_10_1() {
      use malachite::base::num::arithmetic::traits::Abs;
      assert_eq!(Posit::<10, 0, i16>::ZERO.abs(), Posit::<10, 0, i16>::ZERO);
      assert_eq!(Posit::<10, 0, i16>::NAR.abs(), Posit::<10, 0, i16>::NAR);
      for p in Posit::<10, 0, i16>::cases_exhaustive() {
        assert_eq!(Rational::try_from(p.abs()).unwrap(), Rational::try_from(p).unwrap().abs())
      }
    }
  }
}
