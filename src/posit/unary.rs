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
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(p8::round_from(1.).next(), p8::round_from(1.125));
  /// assert_eq!(p8::round_from(128.).next(), p8::round_from(160.));
  /// assert_eq!(p8::MAX.next(), p8::NAR);
  /// assert_eq!(p8::NAR.next(), p8::MIN);
  /// ```
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
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(p8::round_from(1.).prior(), p8::round_from(0.9375));
  /// assert_eq!(p8::round_from(128.).prior(), p8::round_from(112.));
  /// assert_eq!(p8::MIN.prior(), p8::NAR);
  /// assert_eq!(p8::NAR.prior(), p8::MAX);
  /// ```
  #[inline]
  pub fn prior(self) -> Self {
    Self::from_bits(self.0.wrapping_sub(Int::ONE))
  }
}

impl<const N: u32,const ES: u32,Int: crate::Int>
core::ops::Neg for Posit<N, ES, Int> {
  type Output = Posit<N, ES, Int>;

  /// Standard: "**negate**".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(-p16::round_from(3), p16::round_from(-3));
  /// assert_eq!(-p16::MAX, p16::MIN);
  /// ```
  #[inline]
  fn neg(self) -> Self::Output {
    Posit::from_bits(self.0.wrapping_neg())
  }
}

impl<const N: u32,const ES: u32,Int: crate::Int>
core::ops::Neg for &Posit<N, ES, Int> {
  type Output = Posit<N, ES, Int>;

  /// Standard: "**negate**".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(-p16::round_from(3), p16::round_from(-3));
  /// assert_eq!(-p16::MAX, p16::MIN);
  /// ```
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
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(p16::ONE.abs(), p16::MINUS_ONE.abs())
  /// ```
  #[inline]
  pub fn abs(self) -> Self {
    Posit::from_bits(self.0.wrapping_abs())
  }

  /// Return [1](Self::ONE) if `self > 0`, [-1](Self::MINUS_ONE) if `self < 0`, [0](Self::ZERO) if
  /// `self == 0`, and [NaR](Self::NAR) if `self == NaR`.
  ///
  /// Standard: "**sign**".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(p16::round_from(2).sign(), p16::round_from(1));
  /// assert_eq!(p16::round_from(-3).sign(), p16::round_from(-1));
  /// assert_eq!(p16::round_from(0).sign(), p16::round_from(0));
  /// assert_eq!(p16::NAR.sign(), p16::NAR);
  /// ```
  #[inline]
  pub fn sign(self) -> Self {
    // If this is true, `self` is 0 or NaR, so return unchanged.
    if self.is_special() {
      self
    }
    // Otherwise:
    //
    //   +1 is bit pattern 0b0100… 
    //   -1 is bit pattern 0b1100…
    //
    // So we just need to set bits 0 to N-3 to `0`, and bit N-2 to `1`.
    else {
      let bits = self.to_bits() >> (Self::BITS - 2);
      let bits = bits | Int::ONE;
      let bits = bits << (Self::BITS - 2);
      // SAFETY: The junk bits, if any, of `self.to_bits()` are unchanged, so `bits` is still valid
      // input to `from_bits_unchecked`.
      unsafe { Posit::from_bits_unchecked(bits) }
    }
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

  mod sign {
    use super::*;

    #[test]
    fn p8() {
      assert_eq!(crate::p8::ZERO.sign(), crate::p8::ZERO);
      assert_eq!(crate::p8::NAR.sign(), crate::p8::NAR);
      for p in crate::p8::cases_exhaustive() {
        assert_eq!(
          p.sign(),
          if p > Posit::ZERO {Posit::ONE} else {Posit::MINUS_ONE},
        )
      }
    }

    #[test]
    fn posit_10_1() {
      assert_eq!(Posit::<10, 0, i16>::ZERO.sign(), Posit::<10, 0, i16>::ZERO);
      assert_eq!(Posit::<10, 0, i16>::NAR.sign(), Posit::<10, 0, i16>::NAR);
      for p in Posit::<10, 0, i16>::cases_exhaustive() {
        assert_eq!(
          p.sign(),
          if p > Posit::ZERO {Posit::ONE} else {Posit::MINUS_ONE},
        )
      }
    }
  }
}
