use super::*;

impl<
  const N: u32,
  const ES: u32,
  const SIZE: usize,
> Quire<N, ES, SIZE> {
  pub(crate) fn add<Int: crate::Int>(&mut self, posit: Posit<N, ES, Int>) {
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

  pub(crate) fn sub<Int: crate::Int>(&mut self, posit: Posit<N, ES, Int>) {
    self.add(-posit)
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
  const SIZE: usize,
> core::ops::AddAssign<Posit<N, ES, Int>> for Quire<N, ES, SIZE> {
  /// Standard: "**qAddP**".
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
  /// Standard: "**qAddP**".
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
  /// Standard: "**qSubP**".
  fn sub_assign(&mut self, rhs: Posit<N, ES, Int>) {
    self.sub(rhs)
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
  const SIZE: usize,
> core::ops::SubAssign<&Posit<N, ES, Int>> for Quire<N, ES, SIZE> {
  /// Standard: "**qSubP**".
  fn sub_assign(&mut self, rhs: &Posit<N, ES, Int>) {
    self.sub(*rhs)
  }
}

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
      ($name:ident, $posit:ty, $quire:ty,) => {
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
      ($name:ident, $posit:ty, $quire:ty,) => {
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

    /*test_exhaustive!{
      posit_10_0_exhaustive,
      Posit<10, 0, i16>,
      Quire<10, 0, 128>,
    }*/

    test_exhaustive!{
      posit_10_1_exhaustive,
      Posit<10, 1, i16>,
      Quire<10, 1, 128>,
    }

    test_exhaustive!{
      posit_10_2_exhaustive,
      Posit<10, 2, i16>,
      Quire<10, 2, 128>,
    }

    test_exhaustive!{
      posit_10_3_exhaustive,
      Posit<10, 3, i16>,
      Quire<10, 3, 128>,
    }

    /*test_exhaustive!{
      posit_8_0_exhaustive,
      Posit<8, 0, i8>,
      Quire<8, 0, 128>,
    }*/

    test_exhaustive!{
      p8_exhaustive,
      crate::p8,
      crate::q8,
    }

    test_proptest!{
      p16_proptest,
      crate::p16,
      crate::q16,
    }

    test_proptest!{
      p32_proptest,
      crate::p32,
      crate::q32,
    }

    test_proptest!{
      p64_proptest,
      crate::p64,
      crate::q64,
    }

    /*test_exhaustive!{
      posit_3_0_exhaustive,
      Posit<3, 0, i8>,
      Quire<3, 0, 128>,
    }*/

    /*test_exhaustive!{
      posit_4_0_exhaustive,
      Posit<4, 0, i8>,
      Quire<4, 0, 128>,
    }*/

    /*test_exhaustive!{
      posit_4_1_exhaustive,
      Posit<4, 1, i8>,
      Quire<4, 1, 128>,
    }*/
  }

  /// `quire += posit`
  mod quire_posit {
    use super::*;

    macro_rules! test_proptest {
      ($name:ident, $posit:ty, $quire:ty,) => {
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
          #[test]
          fn $name(
            q in <$quire>::cases_proptest_all(),
            p in <$posit>::cases_proptest_all(),
          ) {
            let mut quire = q.clone();
            quire += p;
            match (Rational::try_from(q), Rational::try_from(p)) {
              (Ok(q), Ok(p)) => assert_eq!(Rational::try_from(quire), Ok(q + p)),
              _ => assert!(quire.is_nar()),
            }
          }
        }
      };
    }

    /*test_proptest!{
      posit_10_0_proptest,
      Posit<10, 0, i16>,
      Quire<10, 0, 128>,
    }*/

    test_proptest!{
      posit_10_1_proptest,
      Posit<10, 1, i16>,
      Quire<10, 1, 128>,
    }

    test_proptest!{
      posit_10_2_proptest,
      Posit<10, 2, i16>,
      Quire<10, 2, 128>,
    }

    test_proptest!{
      posit_10_3_proptest,
      Posit<10, 3, i16>,
      Quire<10, 3, 128>,
    }

    /*test_proptest!{
      posit_8_0_proptest,
      Posit<8, 0, i8>,
      Quire<8, 0, 128>,
    }*/

    test_proptest!{
      p8_proptest,
      crate::p8,
      crate::q8,
    }

    test_proptest!{
      p16_proptest,
      crate::p16,
      crate::q16,
    }

    test_proptest!{
      p32_proptest,
      crate::p32,
      crate::q32,
    }

    test_proptest!{
      p64_proptest,
      crate::p64,
      crate::q64,
    }

    /*test_proptest!{
      posit_3_0_proptest,
      Posit<3, 0, i8>,
      Quire<3, 0, 128>,
    }*/

    /*test_proptest!{
      posit_4_0_proptest,
      Posit<4, 0, i8>,
      Quire<4, 0, 128>,
    }*/

    /*test_proptest!{
      posit_4_1_proptest,
      Posit<4, 1, i8>,
      Quire<4, 1, 128>,
    }*/
  }
}
