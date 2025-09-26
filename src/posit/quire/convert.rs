use super::*;
use crate::RoundFrom;

impl<
  const N: u32,
  const ES: u32,
  const SIZE: usize,
> Quire<N, ES, SIZE> {
  /// Aux function: find number of leading 0s or 1s.
  fn leading_run(&self) -> u32 {
    let quire: &[i64] = self.as_int_array();
    let leading = quire[0];
    match leading {
      0 => {
        for i in 1 .. quire.len() {
          if quire[i] != 0 {
            return i as u32 * 64 + quire[i].to_be().leading_zeros()
          }
        }
        return quire.len() as u32 * 64
      },
      -1 => {
        for i in 1 .. quire.len() {
          if quire[i] != -1 {
            return i as u32 * 64 + quire[i].to_be().leading_ones()
          }
        }
        return quire.len() as u32 * 64
      },
      _ => {
        if leading << 1 == 0 {
          1
        } else {
          use crate::underlying::Sealed;
          unsafe { leading.to_be().leading_run_minus_one() + 1 }
        }
      },
    }
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
  const SIZE: usize,
> RoundFrom<&'_ Quire<N, ES, SIZE>> for Posit<N, ES, Int> {
  /// Round a quire back to a posit. This is the final step to do after a series of calculations in
  /// the quire, and the *only* step that actually rounds.
  ///
  /// Standard: "**qToP**".
  fn round_from(value: &'_ Quire<N, ES, SIZE>) -> Self {
    // Find the number of leading 0s or 1s in the quire. This is what will determine the `exp`, as
    // well as the position of the `frac` bits.
    let leading = value.leading_run();
    // If the quire is NaR, the posit to be returned is NaR, of course.
    if leading == 1 && value.is_nar() { return Posit::NAR }

    // The first 1 after the 0s, or the first 0 after the 1s, is `leading` places from the left of
    // the quire. After that, the `Int::BITS` bits that follow are the `frac` of our result. After
    // that, the remaining bits until the end of the quire are the `sticky` bits.
    //
    // Visualised, for an example 8-bit posit:
    //
    //   quire: 1111111111111111111111111|10110101|001110101110101
    //          leading                   frac     sticky
    //
    let leading_ints = leading / Int::BITS;
    let leading_bits = leading % Int::BITS;
    let quire: &[Int] = value.as_int_array();

    // First, the exponent. The "decimal point" of the quire is `BITS - leading - 1` bits from the
    // right, so the difference between that and `WIDTH` is the exponent.
    //
    // There's also a corner case for very large quires: if `BITS - leading` is large enough and
    // `Int` is small enough, the `exp` may overflow the `Int`, so we need to early-return before
    // any casts to `Int`. To ensure this does not introduce a branch where it's not needed
    // (i.e. where there's no risk of any `exp` overflowing), we keep that behind an `if const`.
    let value_width = Quire::<N, ES, SIZE>::BITS - leading;
    if const { Quire::<N, ES, SIZE>::PROD_LIMIT >= 64 } {
      if value_width > 2 * Quire::<N, ES, SIZE>::WIDTH + 1 {
        return if quire[0].to_be().is_positive() {Posit::MAX} else {Posit::MIN}
      }
    }
    let exp = Int::of_u32(value_width) - Int::of_u32(Quire::<N, ES, SIZE>::WIDTH) - Int::ONE;

    // Next, the `frac`. As illustrated above, the `frac` starts after `leading` bits from the left
    // and goes for `Int::BITS`. How we actually wrangle that into one byte depends on the
    // following two cases. To illustrate, assume `Int` is `i8`.
    //
    // - `leading_bits == 0`: Then `frac` is `quire[leading_ints]` shifted 1 place to the right.
    //   The msb of `frac` should be the msb of `quire[leading_ints - 1]`. The lsb of `quire
    //   [leading_ints]` should be accumulated in the `sticky`.
    //
    //   00000000|11000101|10111011|…
    //          [  frac ][sticky
    //
    // - `leading_bits != 0`: Then `frac` is `quire[leading_ints]` shifted `leading_bits - 1`
    //   places to the left. The lowest `leading_bits - 1` bits of `frac` should be the highest
    //   `leading_bits - 1` bits of `quire[leading_ints + 1]`.
    //
    //   00000000|00001100|01011011|…
    //               [  frac ][sticky
    //
    // Besides this, we just need to be careful about a couple of "early return" points, so that we
    // never go out of bounds of the quire.

    // TODO very branchy! Also too many endianness conversions! Revisit later to improve perf
    let frac =
      if leading_bits == 0 {
        // Edge case: if `leading == Quire::SIZE` (i.e. `leading_ints == quire.len()`) then the
        // result can only be 0 or MAX_NEGATIVE.
        if leading_ints as usize == quire.len() {
          // SAFETY: if `leading_ints == quire.len()`, then `quire[0]` has to be 0 or -1, which
          // maps to the bits for `Posit::ZERO` and `Posit::MAX_NEGATIVE`.
          return unsafe { Posit::from_bits_unchecked(quire[0]) }
        }
        let frac_hi = quire[leading_ints as usize - 1] << (Int::BITS - 1);
        let frac_lo = quire[leading_ints as usize].to_be().lshr(1);
        frac_hi | frac_lo
      } else {
        // Edge case: if `leading_ints` is `quire.len() - 1`, then we also need to stop here; it's
        // as if `quire[leading_ints + 1]` was `0`.
        let frac_hi = quire[leading_ints as usize].to_be() << (leading_bits - 1);
        if leading_ints as usize == quire.len() - 1 {
          // SAFETY: `frac` starts with only one leading 0 or 1, and `exp` is in bounds.
          return unsafe { Decoded{frac: frac_hi, exp}.encode_regular() }
        }
        let frac_lo = if leading_bits == 1 {Int::ZERO} else {quire[leading_ints as usize + 1].to_be().lshr(Int::BITS - leading_bits + 1)};
        frac_hi | frac_lo
      };
    let sticky = {
      if leading_ints as usize == quire.len() - 1 {
        Int::ZERO
      } else {
        let sticky_hi = quire[leading_ints as usize + 1].to_be() << leading_bits;
        let mut sticky_lo = Int::ZERO;
        for &i in &quire[leading_ints as usize + 1 ..] {
          sticky_lo |= i
        }
        sticky_hi | sticky_lo | (quire[leading_ints as usize].to_be() & Int::from(leading_bits == 0))
      }
    };

    // SAFETY: `frac` starts with only one leading 0 or 1, and `exp` is in bounds.
    unsafe { Decoded{frac, exp}.encode_regular_round(sticky) }
  }
}

// TODO should we have this alias? :\
/*impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
  const SIZE: usize,
> RoundFrom<Quire<N, ES, SIZE>> for Posit<N, ES, Int> {
  /// Round a quire back to a posit. This is the final step to do after a series of calculations in
  /// the quire, and the *only* step that actually rounds.
  ///
  /// Standard: "**qToP**".
  fn round_from(value: Quire<N, ES, SIZE>) -> Self {
    Self::round_from(&value)
  }
}*/

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
  const SIZE: usize,
> From<Posit<N, ES, Int>> for Quire<N, ES, SIZE> {
  /// Create a quire from a posit value.
  ///
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

  mod from_posit {
    use super::*;

    macro_rules! test_exhaustive {
      ($name:ident, $posit:ty, $quire:ty) => {
        #[test]
        fn $name() {
          for a in <$posit>::cases_exhaustive_all() {
            assert_eq!(Rational::try_from(a), Rational::try_from(<$quire>::from(a)))
          }
        }
      };
    }

    macro_rules! test_proptest {
      ($name:ident, $posit:ty, $quire:ty) => {
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
          #[test]
          fn $name(a in <$posit>::cases_proptest_all()) {
            assert_eq!(Rational::try_from(a), Rational::try_from(<$quire>::from(a)))
          }
        }
      };
    }

    test_exhaustive!{posit_10_0_exhaustive, Posit::<10, 0, i16>, Quire::<10, 0, 128>}
    test_exhaustive!{posit_10_1_exhaustive, Posit::<10, 1, i16>, Quire::<10, 1, 128>}
    test_exhaustive!{posit_10_2_exhaustive, Posit::<10, 2, i16>, Quire::<10, 2, 128>}
    test_exhaustive!{posit_10_3_exhaustive, Posit::<10, 3, i16>, Quire::<10, 3, 128>}
    test_exhaustive!{posit_8_0_exhaustive, Posit::<8, 0, i8>, Quire::<8, 0, 128>}

    test_exhaustive!{p8_exhaustive, crate::p8, crate::q8}
    test_exhaustive!{p16_exhaustive, crate::p16, crate::q16}
    test_proptest!{p32_proptest, crate::p32, crate::q32}
    test_proptest!{p64_proptest, crate::p64, crate::q64}

    test_exhaustive!{posit_3_0_exhaustive, Posit::<3, 0, i8>, Quire::<3, 0, 128>}
    test_exhaustive!{posit_4_0_exhaustive, Posit::<4, 0, i8>, Quire::<4, 0, 128>}
    test_exhaustive!{posit_4_1_exhaustive, Posit::<4, 1, i8>, Quire::<4, 1, 128>}
  }

  mod from_quire {
    use super::*;

    macro_rules! test_proptest {
      ($name:ident, $posit:ty, $quire:ty) => {
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
          #[test]
          fn $name(q in <$quire>::cases_proptest_all()) {
            let posit = <$posit>::round_from(&q);
            let exact = Rational::try_from(q);
            assert!(super::rational::try_is_correct_rounded(exact, posit))
          }
        }
      };
    }

    test_proptest!{posit_10_0_proptest, Posit::<10, 0, i16>, Quire::<10, 0, 128>}
    test_proptest!{posit_10_1_proptest, Posit::<10, 1, i16>, Quire::<10, 1, 128>}
    test_proptest!{posit_10_2_proptest, Posit::<10, 2, i16>, Quire::<10, 2, 128>}
    test_proptest!{posit_10_3_proptest, Posit::<10, 3, i16>, Quire::<10, 3, 128>}
    test_proptest!{posit_8_0_proptest, Posit::<8, 0, i8>, Quire::<8, 0, 128>}

    test_proptest!{p8_proptest, crate::p8, crate::q8}
    test_proptest!{p16_proptest, crate::p16, crate::q16}
    test_proptest!{p32_proptest, crate::p32, crate::q32}
    test_proptest!{p64_proptest, crate::p64, crate::q64}

    test_proptest!{posit_3_0_proptest, Posit::<3, 0, i8>, Quire::<3, 0, 128>}
    test_proptest!{posit_4_0_proptest, Posit::<4, 0, i8>, Quire::<4, 0, 128>}
    test_proptest!{posit_4_1_proptest, Posit::<4, 1, i8>, Quire::<4, 1, 128>}
  }

  mod roundtrip {
    use super::*;

    macro_rules! test_exhaustive {
      ($name:ident, $posit:ty, $quire:ty) => {
        #[test]
        fn $name() {
          for p in <$posit>::cases_exhaustive_all() {
            assert_eq!(p, <$posit>::round_from(&<$quire>::from(p)))
          }
        }
      };
    }

    macro_rules! test_proptest {
      ($name:ident, $posit:ty, $quire:ty) => {
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
          #[test]
          fn $name(p in <$posit>::cases_proptest_all()) {
            assert_eq!(p, <$posit>::round_from(&<$quire>::from(p)))
          }
        }
      };
    }

    test_exhaustive!{posit_10_0_exhaustive, Posit::<10, 0, i16>, Quire::<10, 0, 128>}
    test_exhaustive!{posit_10_1_exhaustive, Posit::<10, 1, i16>, Quire::<10, 1, 128>}
    test_exhaustive!{posit_10_2_exhaustive, Posit::<10, 2, i16>, Quire::<10, 2, 128>}
    test_exhaustive!{posit_10_3_exhaustive, Posit::<10, 3, i16>, Quire::<10, 3, 128>}
    test_exhaustive!{posit_8_0_exhaustive, Posit::<8, 0, i8>, Quire::<8, 0, 128>}

    test_exhaustive!{p8_exhaustive, crate::p8, crate::q8}
    test_exhaustive!{p16_exhaustive, crate::p16, crate::q16}
    test_proptest!{p32_proptest, crate::p32, crate::q32}
    test_proptest!{p64_proptest, crate::p64, crate::q64}

    test_exhaustive!{posit_3_0_exhaustive, Posit::<3, 0, i8>, Quire::<3, 0, 128>}
    test_exhaustive!{posit_4_0_exhaustive, Posit::<4, 0, i8>, Quire::<4, 0, 128>}
    test_exhaustive!{posit_4_1_exhaustive, Posit::<4, 1, i8>, Quire::<4, 1, 128>}
  }
}
