use super::*;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  /// Returns the posit value of the lexicographic successor of `self`'s representation.
  ///
  /// **Standard:** "next".
  pub fn next(self) -> Self {
    Self::from_bits(self.0.wrapping_add(Int::ONE))
  }

  /// Returns the posit value of the lexicographic predecessor of `self`'s representation.
  ///
  /// **Standard:** "prior".
  pub fn prior(self) -> Self {
    Self::from_bits(self.0.wrapping_sub(Int::ONE))
  }
}

impl<const N: u32,const ES: u32,Int: crate::Int>
core::ops::Neg for Posit<N, ES, Int> {
  type Output = Posit<N, ES, Int>;

  fn neg(self) -> Self::Output {
    Posit::from_bits(self.0.wrapping_neg())
  }
}

impl<const N: u32,const ES: u32,Int: crate::Int>
core::ops::Neg for &Posit<N, ES, Int> {
  type Output = Posit<N, ES, Int>;

  fn neg(self) -> Self::Output {
    Posit::from_bits(self.0.wrapping_neg())
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
}
