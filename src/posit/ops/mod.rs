use super::*;

/// Addition and subtraction (both use the same addition algorithm, and `a - b` is simply
/// `a + (-b)`.
mod add;

/// Multiplication.
mod mul;

/// Division.
mod div;

/// Helper macro for implementing operators for all combinations of value and reference
macro_rules! mk_ops {
  ($trait:ident, $trait_assign:ident, $name:ident, $name_assign:ident) => {
    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait<Posit<N, ES, Int>> for Posit<N, ES, Int> {
      type Output = Posit<N, ES, Int>;

      #[inline]
      fn $name(self, rhs: Self) -> Self::Output { self.$name(rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait<&Posit<N, ES, Int>> for Posit<N, ES, Int> {
      type Output = Posit<N, ES, Int>;

      #[inline]
      fn $name(self, rhs: &Self) -> Self::Output { self.$name(*rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait<Posit<N, ES, Int>> for &Posit<N, ES, Int> {
      type Output = Posit<N, ES, Int>;

      #[inline]
      fn $name(self, rhs: Posit<N, ES, Int>) -> Self::Output { (*self).$name(rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait<&Posit<N, ES, Int>> for &Posit<N, ES, Int> {
      type Output = Posit<N, ES, Int>;

      #[inline]
      fn $name(self, rhs: &Posit<N, ES, Int>) -> Self::Output { (*self).$name(*rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait_assign<Posit<N, ES, Int>> for Posit<N, ES, Int> {
      #[inline]
      fn $name_assign(&mut self, rhs: Posit<N, ES, Int>) { *self = self.$name(rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait_assign<&Posit<N, ES, Int>> for Posit<N, ES, Int> {
      #[inline]
      fn $name_assign(&mut self, rhs: &Posit<N, ES, Int>) { *self = self.$name(*rhs) }
    }
  }
}

pub(crate) use mk_ops;

/// Macro for instantating the suite of tests for a binary operator of posits.
macro_rules! mk_tests {
  ($op:tt, $op_assign:tt) => {
    use crate::Posit;
    use malachite::rational::Rational;
    use proptest::prelude::*;

    #[allow(dead_code)]
    fn ops() {
      let mut a = crate::p32::ONE;
      let mut b = crate::p32::MINUS_ONE;
      let _ = a $op b;
      let _ = &a $op b;
      let _ = a $op &b;
      let _ = &a $op &b;
      a $op_assign b;
      b $op_assign &a;
    }

    /// Aux function: check that `a $op b` is rounded correctly.
    fn is_correct_rounded<const N: u32, const ES: u32, Int: crate::Int>(
      a: Posit<N, ES, Int>,
      b: Posit<N, ES, Int>,
    ) -> bool
    where
      Rational: TryFrom<Posit<N, ES, Int>, Error = super::rational::IsNaR>,
    {
      let posit = a $op b;
      if let (Ok(a), Ok(b)) = (Rational::try_from(a), Rational::try_from(b)) {
        if stringify!($op) == "/" && b == Rational::from(0) {
          return posit == Posit::NAR
        }
        let exact = a $op b;
        super::rational::is_correct_rounded(exact, posit)
      } else {
        posit == Posit::NAR
      }
    }

    macro_rules! test_exhaustive {
      ($name:ident, $posit:ty) => {
        #[test]
        fn $name() {
          for a in <$posit>::cases_exhaustive_all() {
            for b in <$posit>::cases_exhaustive_all() {
              assert!(is_correct_rounded(a, b), "{:?} ⋅ {:?}", a, b)
            }
          }
        }
      };
    }

    macro_rules! test_proptest {
      ($name:ident, $posit:ty) => {
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
          #[test]
          fn $name(
            a in <$posit>::cases_proptest_all(),
            b in <$posit>::cases_proptest_all(),
          ) {
            assert!(is_correct_rounded(a, b), "{:?} ⋅ {:?}", a, b)
          }
        }
      };
    }

    test_exhaustive!{posit_10_0_exhaustive, Posit::<10, 0, i16>}
    test_exhaustive!{posit_10_1_exhaustive, Posit::<10, 1, i16>}
    test_exhaustive!{posit_10_2_exhaustive, Posit::<10, 2, i16>}
    test_exhaustive!{posit_10_3_exhaustive, Posit::<10, 3, i16>}

    test_exhaustive!{posit_8_0_exhaustive, Posit::<8, 0, i8>}

    // Above ~10 bits = 2^20 operations, it's infeasible to test binary operations exhaustively,
    // especially when not in a release build (in that case, we maybe can go to ~16 bits = 2^32).
    test_exhaustive!{p8_exhaustive, crate::p8}
    test_proptest!{p16_proptest, crate::p16}
    test_proptest!{p32_proptest, crate::p32}
    test_proptest!{p64_proptest, crate::p64}

    test_exhaustive!{posit_3_0_exhaustive, Posit::<3, 0, i8>}
    test_exhaustive!{posit_4_0_exhaustive, Posit::<4, 0, i8>}
    test_exhaustive!{posit_4_1_exhaustive, Posit::<4, 1, i8>}
  }
}

pub(crate) use mk_tests;
