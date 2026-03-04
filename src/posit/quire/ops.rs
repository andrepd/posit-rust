use super::*;

impl<
  const N: u32,
  const ES: u32,
  const SIZE: usize,
> Quire<N, ES, SIZE> {
  fn add<Int: crate::Int>(&mut self, posit: Posit<N, ES, Int>) {
    if posit == Posit::ZERO {
      ()
    } else if posit == Posit::NAR || self.is_nar() {
      *self = Quire::NAR
    } else {
      // SAFETY: `posit` is not 0 or NaR
      let decoded = unsafe { posit.decode_regular() };
      // SAFETY: `decoded` comes from `Posit::decode_regular`, therefore its `exp` is in bounds
      unsafe { self.accumulate_decoded(decoded) }
    }
  }

  fn add_quire(&mut self, quire: &Quire<N, ES, SIZE>) {
    if self.is_nar() {
      ()
    } else if crate::utl::unlikely(quire.is_nar()) {
      *self = Self::NAR
    } else {
      // TODO replace `accumulate_slice` with `accumulate` if ever `min_generic_const_args` is
      // stabilised!
      // SAFETY: `Self::SIZE` == `quire::SIZE`.
      unsafe { self.accumulate_slice(quire.as_u64_array(), 0) }
    }
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
  const SIZE: usize,
> core::ops::AddAssign<Posit<N, ES, Int>> for Quire<N, ES, SIZE> {
  /// Standard: "[**qAddP**](https://posithub.org/docs/posit_standard-2.pdf#subsection.5.11)".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// let mut quire = q16::from(p16::ONE);
  /// quire += p16::round_from(0.42);
  /// assert_eq!(p16::round_from(1.42), (&quire).round_into())
  /// ```
  fn add_assign(&mut self, rhs: Posit<N, ES, Int>) {
    self.add(rhs)
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
  const SIZE: usize,
> core::ops::AddAssign<&Posit<N, ES, Int>> for Quire<N, ES, SIZE> {
  /// Standard: "[**qAddP**](https://posithub.org/docs/posit_standard-2.pdf#subsection.5.11)".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// let mut quire = q16::from(p16::ONE);
  /// quire += p16::round_from(0.42);
  /// assert_eq!(p16::round_from(1.42), (&quire).round_into())
  /// ```
  fn add_assign(&mut self, rhs: &Posit<N, ES, Int>) {
    self.add(*rhs)
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
  const SIZE: usize,
> core::ops::SubAssign<Posit<N, ES, Int>> for Quire<N, ES, SIZE> {
  /// Standard: "[**qSubP**](https://posithub.org/docs/posit_standard-2.pdf#subsection.5.11)".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// let mut quire = q16::from(p16::ONE);
  /// quire -= p16::round_from(0.42);
  /// assert_eq!(p16::round_from(0.58), (&quire).round_into())
  /// ```
  fn sub_assign(&mut self, rhs: Posit<N, ES, Int>) {
    self.add(-rhs)
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
  const SIZE: usize,
> core::ops::SubAssign<&Posit<N, ES, Int>> for Quire<N, ES, SIZE> {
  /// Standard: "[**qSubP**](https://posithub.org/docs/posit_standard-2.pdf#subsection.5.11)".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// let mut quire = q16::from(p16::ONE);
  /// quire -= p16::round_from(0.42);
  /// assert_eq!(p16::round_from(0.58), (&quire).round_into())
  /// ```
  fn sub_assign(&mut self, rhs: &Posit<N, ES, Int>) {
    self.add(-*rhs)
  }
}

impl<
  const N: u32,
  const ES: u32,
  const SIZE: usize,
> core::ops::AddAssign<&Quire<N, ES, SIZE>> for Quire<N, ES, SIZE> {
  /// Standard: "[**qAddQ**](https://posithub.org/docs/posit_standard-2.pdf#subsection.5.11)".
  fn add_assign(&mut self, rhs: &Quire<N, ES, SIZE>) {
    self.add_quire(rhs)
  }
}

/*impl<
  const N: u32,
  const ES: u32,
  const SIZE: usize,
> core::ops::SubAssign<&Quire<N, ES, SIZE>> for Quire<N, ES, SIZE> {
  /// Standard: "[**qSubQ**](https://posithub.org/docs/posit_standard-2.pdf#subsection.5.11)".
  fn sub_assign(&mut self, rhs: &Quire<N, ES, SIZE>) {
    self.add_quire(todo!())
  }
}*/

#[cfg(test)]
mod tests {
  use super::*;
  use malachite::rational::Rational;
  use proptest::prelude::*;

  /// `Quire::from(posit) += posit`
  mod posit_posit {
    // TODO these tests are basic: they test for two posits a and b whether summing them on the quire
    // yields the correct result. But more tests are needed: summing vectors of n posits, not just 2.
    use super::*;

    macro_rules! test_exhaustive {
      ($name:ident, $posit:ty, $quire:ty) => {
        #[test]
        fn $name() {
          for a in <$posit>::cases_exhaustive_all() {
            for b in <$posit>::cases_exhaustive_all() {
              let posit = a + b;
              let mut quire = <$quire>::from(a);
              quire += b;
              assert!(super::rational::try_is_correct_rounded(Rational::try_from(quire), posit))
            }
          }
        }
      };
    }

    macro_rules! test_proptest {
      ($name:ident, $posit:ty, $quire:ty) => {
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
          #[test]
          fn $name(
            a in <$posit>::cases_proptest_all(),
            b in <$posit>::cases_proptest_all(),
          ) {
            let posit = a + b;
            let mut quire = <$quire>::from(a);
            quire += b;
            assert!(super::rational::try_is_correct_rounded(Rational::try_from(quire), posit))
          }
        }
      };
    }

    test_exhaustive!{posit_10_0_exhaustive, Posit<10, 0, i16>, Quire<10, 0, 128>}
    test_exhaustive!{posit_10_1_exhaustive, Posit<10, 1, i16>, Quire<10, 1, 128>}
    test_exhaustive!{posit_10_2_exhaustive, Posit<10, 2, i16>, Quire<10, 2, 128>}
    test_exhaustive!{posit_10_3_exhaustive, Posit<10, 3, i16>, Quire<10, 3, 128>}
    test_exhaustive!{posit_8_0_exhaustive, Posit<8, 0, i8>, Quire<8, 0, 128>}

    test_exhaustive!{p8_exhaustive, crate::p8, crate::q8}
    test_proptest!{p16_proptest, crate::p16, crate::q16}
    test_proptest!{p32_proptest, crate::p32, crate::q32}
    test_proptest!{p64_proptest, crate::p64, crate::q64}

    test_exhaustive!{posit_3_0_exhaustive, Posit<3, 0, i8>, Quire<3, 0, 128>}
    test_exhaustive!{posit_4_0_exhaustive, Posit<4, 0, i8>, Quire<4, 0, 128>}
    test_exhaustive!{posit_4_1_exhaustive, Posit<4, 1, i8>, Quire<4, 1, 128>}
  }

  /// `quire += posit`
  mod quire_posit {
    use super::*;

    /// Manual test for overflowing the quire sum limit on the positive side
    #[test]
    fn q8_overflow_positive() {
      use crate::{p8, q8};
      let mut quire = q8::MAX;
      assert!(!quire.is_nar());
      quire -= p8::ONE;
      assert!(!quire.is_nar());
      quire += p8::ONE;
      assert!(!quire.is_nar());
      quire += p8::ONE;
      assert!(quire.is_nar());
    }

    /// Manual test for overflowing the quire sum limit on the negative side
    #[test]
    fn q8_overflow_negative() {
      use crate::{p8, q8};
      let mut quire = q8::MIN;
      assert!(!quire.is_nar());
      quire += p8::ONE;
      assert!(!quire.is_nar());
      quire -= p8::ONE;
      assert!(!quire.is_nar());
      quire -= p8::ONE;
      assert!(quire.is_nar());
    }

    macro_rules! test_proptest {
      ($name:ident, $posit:ty, $quire:ty) => {
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
          #[test]
          fn $name(
            q in <$quire>::cases_proptest_all(),
            p in <$posit>::cases_proptest_all(),
          ) {
            let mut sum = q.clone();
            sum += p;
            match (Rational::try_from(q), Rational::try_from(p)) {
              (Ok(q), Ok(p)) => assert!(super::rational::quire_is_correct_rounded(q + p, sum)),
              _ => assert!(sum.is_nar()),
            }
          }
        }
      };
    }

    test_proptest!{posit_10_0_proptest, Posit<10, 0, i16>, Quire<10, 0, 128>}
    test_proptest!{posit_10_1_proptest, Posit<10, 1, i16>, Quire<10, 1, 128>}
    test_proptest!{posit_10_2_proptest, Posit<10, 2, i16>, Quire<10, 2, 128>}
    test_proptest!{posit_10_3_proptest, Posit<10, 3, i16>, Quire<10, 3, 128>}
    test_proptest!{posit_8_0_proptest, Posit<8, 0, i8>, Quire<8, 0, 128>}

    test_proptest!{p8_proptest, crate::p8, crate::q8}
    test_proptest!{p16_proptest, crate::p16, crate::q16}
    test_proptest!{p32_proptest, crate::p32, crate::q32}
    test_proptest!{p64_proptest, crate::p64, crate::q64}

    test_proptest!{posit_3_0_proptest, Posit<3, 0, i8>, Quire<3, 0, 128>}
    test_proptest!{posit_4_0_proptest, Posit<4, 0, i8>, Quire<4, 0, 128>}
    test_proptest!{posit_4_1_proptest, Posit<4, 1, i8>, Quire<4, 1, 128>}
  }

  /// `quire += quire`
  mod quire_quire {
    use super::*;

    #[test]
    fn q32_overflow_positive() {
      use crate::RoundFrom;
      let mut quire = crate::q32::MAX;
      assert!(!quire.is_nar());
      quire += &crate::q32::from(crate::p32::round_from(1e-9));
      assert!(quire.is_nar())
    }

    #[test]
    fn q32_overflow_negative() {
      use crate::RoundFrom;
      let mut quire = crate::q32::MIN;
      assert!(!quire.is_nar());
      quire += &crate::q32::from(crate::p32::round_from(-1e-9));
      assert!(quire.is_nar())
    }

    macro_rules! test_proptest {
      ($name:ident, $quire:ty) => {
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
          #[test]
          fn $name(
            a in <$quire>::cases_proptest_all(),
            b in <$quire>::cases_proptest_all(),
          ) {
            let mut sum = a.clone();
            sum += &b;
            match (Rational::try_from(a), Rational::try_from(b)) {
              (Ok(a), Ok(b)) => assert!(super::rational::quire_is_correct_rounded(a + b, sum)),
              _ => assert!(sum.is_nar()),
            }
          }
        }
      };
    }

    test_proptest!{posit_10_0_proptest, Quire<10, 0, 128>}
    test_proptest!{posit_10_1_proptest, Quire<10, 1, 128>}
    test_proptest!{posit_10_2_proptest, Quire<10, 2, 128>}
    test_proptest!{posit_10_3_proptest, Quire<10, 3, 128>}
    test_proptest!{posit_8_0_proptest, Quire<8, 0, 128>}

    test_proptest!{p8_proptest, crate::q8}
    test_proptest!{p16_proptest, crate::q16}
    test_proptest!{p32_proptest, crate::q32}
    test_proptest!{p64_proptest, crate::q64}

    test_proptest!{posit_3_0_proptest, Quire<3, 0, 128>}
    test_proptest!{posit_4_0_proptest, Quire<4, 0, 128>}
    test_proptest!{posit_4_1_proptest, Quire<4, 1, 128>}
  }
}
