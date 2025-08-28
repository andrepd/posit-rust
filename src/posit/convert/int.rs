use super::*;

use crate::underlying::const_as;

/// The kernel for converting a signed int to a posit.
///
/// If `value` is `FromInt::MIN`, calling this function is *undefined behaviour*.
unsafe fn round_from_signed<
  FromInt: crate::Int,
  const N: u32,
  const ES: u32,
  Int: crate::Int,
>(int: FromInt) -> Posit<N, ES, Int> {
  if int == FromInt::ZERO { return Posit::ZERO }

  // If converting into a narrower type (`FromInt` → `Int`), we need to shift right, *before* we
  // convert to the narrower type. Some bits will be lost in this conversion; we will accumulate
  // them into `sticky`.
  let shift_right = if const { Int::BITS >= FromInt::BITS } {0} else {FromInt::BITS - Int::BITS};

  // If converting into a wider type (`FromInt` → `Int`), we need to shift left, *after* we convert
  // to the wider type.
  let shift_left = if const { Int::BITS <= FromInt::BITS } {0} else {Int::BITS - FromInt::BITS};

  // To turn the `int` into a `frac` that starts with `0b01` or `0b10`, find the number of leading
  // 0s or 1s, and shift left by that number of places minus one. To compensate, the `exp` has to
  // be `FRAC_WIDTH` subtracted by the number of places we shifted. The `sticky` bits are the bits
  // lost when shifting right.
  //
  // Examples:
  //
  //   value: 0b00010011 (= 19)
  //    frac: 0b01001100
  //     exp: +4 (= (8 - 2) frac width - 2 underflow)
  //
  //   value: 0b11111111 (= -1)
  //    frac: 0b10000000
  //     exp: -1 (= (8 - 2) frac width - 7 underflow)
  //
  // SAFETY: `int` is not 0 (we checked) and not MIN (function precondition)
  let underflow = unsafe { int.leading_run_minus_one() };
  let frac = const_as::<FromInt, Int>(int << underflow >> shift_right) << shift_left;
  let exp = const_as::<i32, Int>(Decoded::<N, ES, FromInt>::FRAC_WIDTH.wrapping_sub(underflow) as i32);
  let sticky = Int::from(int.mask_lsb(shift_right.saturating_sub(underflow)) != FromInt::ZERO);

  // This piece of code is only necessary in really extreme cases, like converting i128::MAX into
  // an 8-bit posit. But in those cases, we do need to guard against overflow on `exp`.
  if const { FromInt::BITS as i128 > 1 << Decoded::<N, ES, Int>::FRAC_WIDTH } {
    let limit = FromInt::ONE << (1 << Decoded::<N, ES, Int>::FRAC_WIDTH);
    if int >= limit { return Posit::MAX }
    if int <= -limit { return Posit::MIN }
  }

  // SAFETY: `frac` is not underflowing and `exp` cannot be greater than `FromInt::BITS`.
  unsafe { Decoded{frac, exp}.encode_regular_round(sticky) }
}

macro_rules! make_impl {
  ($t:ty) => {
    impl<
      const N: u32,
      const ES: u32,
      Int: crate::Int,
    > RoundFrom<$t> for Posit<N, ES, Int> {
      #[doc = concat!("Convert an `", stringify!($t), "` into a `Posit`, [rounding according to the standard]:")]
      #[doc = ""]
      #[doc = concat!("  - If the value is [`", stringify!($t), "::MIN`] (i.e. the value where the most significant bit is 1 and the rest are 0), it converts to [`NaR`](Posit::NAR).")]
      #[doc = "  - Otherwise, the integer value is rounded (if necessary)."]
      #[doc = ""]
      #[doc = "[rounding according to the standard]: https://posithub.org/docs/posit_standard-2.pdf#subsection.6.4"]
      fn round_from(value: $t) -> Self {
        if value == <$t>::MIN {
          return Self::NAR
        } else {
          // SAFETY: `value` is not NAR
          unsafe { round_from_signed(value) }
        }
      }
    }    
  }
}

make_impl!{i8}
make_impl!{i16}
make_impl!{i32}
make_impl!{i64}
make_impl!{i128}

// TODO unsigned

#[cfg(test)]
mod tests {
  use super::*;
  use malachite::rational::Rational;
  use proptest::prelude::*;

  /// Aux function: check that `int` is converted to a posit with the correct rounding.
  fn is_correct_rounded<FromInt: crate::Int, const N: u32, const ES: u32, Int: crate::Int>(
    int: FromInt,
  ) -> bool
  where
    FromInt: Into<Rational> + RoundInto<Posit<N, ES, Int>>,
    Rational: TryFrom<Posit<N, ES, Int>>,
    <Rational as TryFrom<Posit<N, ES, Int>>>::Error: core::fmt::Debug
  {
    let posit: Posit<N, ES, Int> = int.round_into();
    if int == FromInt::MIN {
      posit == Posit::NAR
    } else {
      let exact: Rational = int.into();
      super::rational::is_correct_rounded(exact, posit)
    }
  }

  macro_rules! make_exhaustive {
    ($t:ident) => {
      mod $t {
        use super::*;

        #[test]
        fn posit_10_0_exhaustive() {
          for int in $t::MIN .. $t::MAX {
            assert!(is_correct_rounded::<$t, 10, 0, i16>(int), "{:?}", int)
          }
        }

        #[test]
        fn posit_10_1_exhaustive() {
          for int in $t::MIN .. $t::MAX {
            assert!(is_correct_rounded::<$t, 10, 1, i16>(int), "{:?}", int)
          }
        }

        #[test]
        fn posit_10_2_exhaustive() {
          for int in $t::MIN .. $t::MAX {
            assert!(is_correct_rounded::<$t, 10, 2, i16>(int), "{:?}", int)
          }
        }

        #[test]
        fn posit_10_3_exhaustive() {
          for int in $t::MIN .. $t::MAX {
            assert!(is_correct_rounded::<$t, 10, 3, i16>(int), "{:?}", int)
          }
        }

        #[test]
        fn posit_8_0_exhaustive() {
          for int in $t::MIN .. $t::MAX {
            assert!(is_correct_rounded::<$t, 8, 0, i8>(int), "{:?}", int)
          }
        }

        #[test]
        fn p8_exhaustive() {
          for int in $t::MIN .. $t::MAX {
            assert!(is_correct_rounded::<$t, 8, 2, i8>(int), "{:?}", int)
          }
        }

        #[test]
        fn p16_exhaustive() {
          for int in $t::MIN .. $t::MAX {
            assert!(is_correct_rounded::<$t, 16, 2, i16>(int), "{:?}", int)
          }
        }

        #[test]
        fn p32_exhaustive() {
          for int in $t::MIN .. $t::MAX {
            assert!(is_correct_rounded::<$t, 32, 2, i32>(int), "{:?}", int)
          }
        }

        #[test]
        fn p64_exhaustive() {
          for int in $t::MIN .. $t::MAX {
            assert!(is_correct_rounded::<$t, 64, 2, i64>(int), "{:?}", int)
          }
        }
      }
    }
  }

  macro_rules! make_proptest {
    ($t:ident) => {
      mod $t {
        use super::*;

        const PROPTEST_CASES: u32 = if cfg!(debug_assertions) {0x1_0000} else {0x80_0000};
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(PROPTEST_CASES))]

          #[test]
          fn posit_10_0_proptest(int in any::<$t>()) {
            assert!(is_correct_rounded::<$t, 10, 0, i16>(int), "{:?}", int)
          }

          #[test]
          fn posit_10_1_proptest(int in any::<$t>()) {
            assert!(is_correct_rounded::<$t, 10, 1, i16>(int), "{:?}", int)
          }

          #[test]
          fn posit_10_2_proptest(int in any::<$t>()) {
            assert!(is_correct_rounded::<$t, 10, 2, i16>(int), "{:?}", int)
          }

          #[test]
          fn posit_10_3_proptest(int in any::<$t>()) {
            assert!(is_correct_rounded::<$t, 10, 3, i16>(int), "{:?}", int)
          }

          #[test]
          fn posit_8_0_proptest(int in any::<$t>()) {
            assert!(is_correct_rounded::<$t, 8, 0, i8>(int), "{:?}", int)
          }

          #[test]
          fn p8_proptest(int in any::<$t>()) {
            assert!(is_correct_rounded::<$t, 8, 2, i8>(int), "{:?}", int)
          }

          #[test]
          fn p16_proptest(int in any::<$t>()) {
            assert!(is_correct_rounded::<$t, 16, 2, i16>(int), "{:?}", int)
          }

          #[test]
          fn p32_proptest(int in any::<$t>()) {
            assert!(is_correct_rounded::<$t, 32, 2, i32>(int), "{:?}", int)
          }

          #[test]
          fn p64_proptest(int in any::<$t>()) {
            assert!(is_correct_rounded::<$t, 64, 2, i64>(int), "{:?}", int)
          }
        }
      }
    }
  }

  make_exhaustive!{i8}
  make_exhaustive!{i16}
  make_proptest!{i32}
  make_proptest!{i64}
  make_proptest!{i128}
}