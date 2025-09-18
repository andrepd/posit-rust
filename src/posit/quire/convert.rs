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

  /*#[test]
  fn posit_10_0_exhaustive() {
    type P = Posit::<10, 0, i16>;
    type Q = Quire::<10, 0, 128>;
    for a in P::cases_exhaustive_all() {
      assert_eq!(Rational::try_from(a), Rational::try_from(Q::from(a)))
    }
  }*/

  #[test]
  fn posit_10_1_exhaustive() {
    type P = Posit::<10, 1, i16>;
    type Q = Quire::<10, 1, 128>;
    for a in P::cases_exhaustive_all() {
      assert_eq!(Rational::try_from(a), Rational::try_from(Q::from(a)))
    }
  }

  #[test]
  fn posit_10_2_exhaustive() {
    type P = Posit::<10, 2, i16>;
    type Q = Quire::<10, 2, 128>;
    for a in P::cases_exhaustive_all() {
      assert_eq!(Rational::try_from(a), Rational::try_from(Q::from(a)))
    }
  }

  #[test]
  fn posit_10_3_exhaustive() {
    type P = Posit::<10, 3, i16>;
    type Q = Quire::<10, 3, 128>;
    for a in P::cases_exhaustive_all() {
      assert_eq!(Rational::try_from(a), Rational::try_from(Q::from(a)))
    }
  }

  /*#[test]
  fn posit_8_0_exhaustive() {
    type P = Posit::<8, 0, i8>;
    type Q = Quire::<8, 0, 128>;
    for a in P::cases_exhaustive_all() {
      assert_eq!(Rational::try_from(a), Rational::try_from(Q::from(a)))
    }
  }*/

  #[test]
  fn p8_exhaustive() {
    for a in crate::p8::cases_exhaustive_all() {
      assert_eq!(Rational::try_from(a), Rational::try_from(crate::q8::from(a)))
    }
  }

  #[test]
  fn p16_exhaustive() {
    for a in crate::p16::cases_exhaustive_all() {
      assert_eq!(Rational::try_from(a), Rational::try_from(crate::q16::from(a)))
    }
  }

  use proptest::prelude::*;
  const PROPTEST_CASES: u32 = if cfg!(debug_assertions) {0x1_0000} else {0x80_0000};
  proptest!{
    #![proptest_config(ProptestConfig::with_cases(PROPTEST_CASES))]

    #[test]
    fn p32_proptest(a in crate::p32::cases_proptest()) {
      assert_eq!(Rational::try_from(a), Rational::try_from(crate::q32::from(a)))
    }

    #[test]
    fn p64_proptest(a in crate::p64::cases_proptest()) {
      assert_eq!(Rational::try_from(a), Rational::try_from(crate::q64::from(a)))
    }
  }

  /*#[test]
  fn posit_3_0_exhaustive() {
    type P = Posit::<3, 0, i8>;
    type Q = Quire::<3, 0, 128>;
    for a in P::cases_exhaustive_all() {
      assert_eq!(Rational::try_from(a), Rational::try_from(Q::from(a)))
    }
  }*/

  /*#[test]
  fn posit_4_0_exhaustive() {
    type P = Posit::<4, 0, i8>;
    type Q = Quire::<4, 0, 128>;
    for a in P::cases_exhaustive_all() {
      assert_eq!(Rational::try_from(a), Rational::try_from(Q::from(a)))
    }
  }*/

  /*#[test]
  fn posit_4_1_exhaustive() {
    type P = Posit::<4, 1, i8>;
    type Q = Quire::<4, 1, 128>;
    for a in P::cases_exhaustive_all() {
      assert_eq!(Rational::try_from(a), Rational::try_from(Q::from(a)))
    }
  }*/
}
