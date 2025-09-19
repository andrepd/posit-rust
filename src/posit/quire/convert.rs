use super::*;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
  const SIZE: usize,
> From<Posit<N, ES, Int>> for Quire<N, ES, SIZE> {
  /// Standard: "**pToQ**".
  fn from(value: Posit<N, ES, Int>) -> Self {
    if value == Posit::ZERO {
      Self::ZERO
    } else if value == Posit::NAR {
      Self::NAR
    } else {
      let mut quire = Self::ZERO;
      // SAFETY: `value` is not 0 or NaR
      let decoded = unsafe { value.decode_regular() };
      // SAFETY: `decoded` comes from `Posit::decode_regular`, therefore its `exp` is in bounds
      unsafe { quire.accumulate_decoded(decoded) };
      quire
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use malachite::rational::Rational;
  use proptest::prelude::*;

  macro_rules! test_exhaustive {
    ($name:ident, $posit:ty, $quire:ty,) => {
      #[test]
      fn $name() {
        for a in <$posit>::cases_exhaustive_all() {
          assert_eq!(Rational::try_from(a), Rational::try_from(<$quire>::from(a)))
        }
      }
    };
  }

  macro_rules! test_proptest {
    ($name:ident, $posit:ty, $quire:ty,) => {
      proptest!{
        #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
        #[test]
        fn $name(a in <$posit>::cases_proptest_all()) {
          assert_eq!(Rational::try_from(a), Rational::try_from(<$quire>::from(a)))
        }
      }
    };
  }

  /*test_exhaustive!{
    posit_10_0_exhaustive,
    Posit::<10, 0, i16>,
    Quire::<10, 0, 128>,
  }*/

  test_exhaustive!{
    posit_10_1_exhaustive,
    Posit::<10, 1, i16>,
    Quire::<10, 1, 128>,
  }

  test_exhaustive!{
    posit_10_2_exhaustive,
    Posit::<10, 2, i16>,
    Quire::<10, 2, 128>,
  }

  test_exhaustive!{
    posit_10_3_exhaustive,
    Posit::<10, 3, i16>,
    Quire::<10, 3, 128>,
  }

  /*test_exhaustive!{
    posit_8_0_exhaustive,
    Posit::<8, 0, i8>,
    Quire::<8, 0, 128>,
  }*/

  test_exhaustive!{
    p8_exhaustive,
    crate::p8,
    crate::q8,
  }

  test_exhaustive!{
    p16_exhaustive,
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
    Posit::<3, 0, i8>,
    Quire::<3, 0, 128>,
  }*/

  /*test_exhaustive!{
    posit_4_0_exhaustive,
    Posit::<4, 0, i8>,
    Quire::<4, 0, 128>,
  }*/

  /*test_exhaustive!{
    posit_4_1_exhaustive,
    Posit::<4, 1, i8>,
    Quire::<4, 1, 128>,
  }*/
}
