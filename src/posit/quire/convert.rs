use super::*;
use crate::RoundFrom;

impl<
  const N: u32,
  const ES: u32,
  const SIZE: usize,
> Quire<N, ES, SIZE> {
  /// Aux function: find number of leading 0s or 1s.
  fn leading_run(&self) -> u32 {
    let quire: &[u64] = self.as_u64_array();
    let idx_last = quire.len() - 1;
    match quire[idx_last] as i64 >= 0 {
      true => {
        for i in 0 .. quire.len() {
          if quire[idx_last - i] != 0 {
            return i as u32 * 64 + quire[idx_last - i].leading_zeros()
          }
        }
        return quire.len() as u32 * 64
      },
      false => {
        for i in 0 .. quire.len() {
          if quire[idx_last - i] != u64::MAX {
            return i as u32 * 64 + quire[idx_last - i].leading_ones()
          }
        }
        return quire.len() as u32 * 64
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
  /// Standard: "[**qToP**](https://posithub.org/docs/posit_standard-2.pdf#subsection.5.11)".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// let mut quire = q16::from(p16::MAX);
  /// quire += p16::round_from(0.1);
  /// quire -= p16::MAX;
  /// let result: p16 = (&quire).round_into();
  /// assert_eq!(result, p16::round_from(0.1))
  /// ```
  fn round_from(value: &'_ Quire<N, ES, SIZE>) -> Self {
    const { assert!(Int::BITS <= 64, "Only posits up to 64 bits are currently supported") };

    // If the quire is NaR, the posit to be returned is NaR, of course.
    if value.is_nar() { return Posit::NAR }
    // Find the number of leading 0s or 1s in the quire, minus one. This is what will determine the
    // `exp`, as well as the position of the `frac` bits.
    let leading = value.leading_run() - 1;

    // If `leading` is `Quire::BITS - 1`, then the quire is all 0s or all 1s. This maps to
    // Posit::ZERO and POSIT::MIN, respectively, which are also all 0s or all 1s.
    if leading + 1 == Quire::<N, ES, SIZE>::BITS {
      // SAFETY: The size of `Quire` is greater than that of `Posit`.
      return unsafe { core::mem::transmute_copy(value) }
    }

    // The first `01` or `10` sequence is `leading` places from the left of the quire (remember,
    // "left" as in "most-significant", even though the bytes are stored little endian therefore
    // the msb of the quire is at the end of the array). After that, the `Int::BITS` bits that
    // follow are the `frac` of our result. After that, the remaining bits until the end of the
    // quire are the `sticky` bits.
    //
    // Visualised, for an example 8-bit posit, with leading=25, and commas marking the 8-bit
    // boundaries:
    //
    //   quire: 11111111,11111111,11111111,1|1011010,1|0011101,01110101
    //          leading                   frac     sticky
    //
    let leading_ints = (leading / Int::BITS) as usize;
    let leading_bits = (leading % Int::BITS) as u32;
    let quire: &[Int] = value.as_int_array();
    let idx_last = quire.len() - 1;

    // First, the exponent. The "decimal point" of the quire is `BITS - leading - 2` bits from the
    // right, so the difference between that and `WIDTH` is the exponent.
    //
    // There's also a corner case for very large quires: if `BITS - leading` is large enough and
    // `Int` is small enough, the `exp` may overflow the `Int`, so we need to early-return before
    // any casts to `Int`. To ensure this does not introduce a branch where it's not needed
    // (i.e. where there's no risk of any `exp` overflowing), we keep that behind an `if const`.
    let value_width = Quire::<N, ES, SIZE>::BITS - leading;
    if const { Int::BITS <= 8 } {
      if value_width > 2 * Quire::<N, ES, SIZE>::WIDTH + 1 {
        return if quire[idx_last].is_positive() {Posit::MAX} else {Posit::MIN}
      }
    }
    let exp = Int::of_u32(value_width) - Int::of_u32(Quire::<N, ES, SIZE>::WIDTH) - Int::ONE - Int::ONE;

    // Next, the `frac`. As illustrated above, the `frac` starts after `leading` bits from the left
    // and goes for `Int::BITS`. How we actually wrangle that into one Int depends on the
    // following two cases. To illustrate, assume `Int` is `i8`.
    //
    // - `leading_bits == 0`: Then `frac` is exactly `quire[leading_ints]`. Any further bytes to
    //   the right should be accumulated in the `sticky`.
    //
    //   00000000|01100010|10111011|…    leading_ints = 1
    //            [ frac ] [   sticky    leading_bits = 0
    //
    // - `leading_bits != 0`: Then `frac` is `quire[leading_ints]` shifted `leading_bits - 1`
    //   places to the left. The lowest `leading_bits - 1` bits of `frac` should be the highest
    //   `leading_bits - 1` bits of `quire[leading_ints + 1]`.
    //
    //   00000000|00001100|01011011|…     leading_ints = 1
    //               [ frac  ][sticky     leading_bits = 3
    //
    // Besides this, we just need to be careful about a couple of edge cases, so that we never go
    // out of bounds.
    let frac = {
      let frac_hi = quire[idx_last - leading_ints] << leading_bits;
      // Edge case: if `leading_ints` is `idx_last`, then we also need to stop here; it's as if
      // `quire[idx_last - leading_ints - 1]` was `0`.
      let frac_lo = if leading_bits != 0 && leading_ints < idx_last {
        quire[idx_last - leading_ints - 1].lshr(Int::BITS - leading_bits)
      } else {
        Int::ZERO
      };
      frac_hi | frac_lo
    };
    let sticky = {
      // Again, if `leading_ints` is `idx_last`, then we must stop here.
      let sticky_hi = if leading_ints < idx_last {
        quire[idx_last - leading_ints - 1] << leading_bits
      } else {
        Int::ZERO
      };
      let mut sticky_lo = Int::ZERO;
      if leading_ints < idx_last - 1 {
        for &i in &quire[.. idx_last - leading_ints - 2] {
          sticky_lo |= i
        }
      }
      sticky_hi | sticky_lo
    };

    // SAFETY: `frac` starts with only one leading 0 or 1, and `exp` is in bounds.
    unsafe { Decoded{frac, exp}.encode_regular_round(sticky) }
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
  const SIZE: usize,
> RoundFrom<Quire<N, ES, SIZE>> for Posit<N, ES, Int> {
  /// Round a quire back to a posit. This is the final step to do after a series of calculations in
  /// the quire, and the *only* step that actually rounds.
  ///
  /// Standard: "[**qToP**](https://posithub.org/docs/posit_standard-2.pdf#subsection.5.11)".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// let mut quire = q16::from(p16::MAX);
  /// quire += p16::round_from(0.1);
  /// quire -= p16::MAX;
  /// let result: p16 = quire.round_into();
  /// assert_eq!(result, p16::round_from(0.1))
  /// ```
  #[inline]
  fn round_from(value: Quire<N, ES, SIZE>) -> Self {
    Self::round_from(&value)
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
  const SIZE: usize,
> From<Posit<N, ES, Int>> for Quire<N, ES, SIZE> {
  /// Create a quire from a posit value.
  ///
  /// Standard: "[**pToQ**](https://posithub.org/docs/posit_standard-2.pdf#subsection.5.11)".
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// let posit = p16::round_from(123);
  /// let quire = q16::from(posit);
  /// ```
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

  #[test]
  fn leading_run_3() {
    let bytes = [
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0b00010000,
    ];
    assert_eq!(3, crate::q16::from_bits(bytes).leading_run());
    let bytes = [
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0b11100000,
    ];
    assert_eq!(3, crate::q16::from_bits(bytes).leading_run());
  }

  #[test]
  fn leading_run_1() {
    let bytes = [
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0b01001101,
    ];
    assert_eq!(1, crate::q16::from_bits(bytes).leading_run());
    let bytes = [
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0b10000000,
    ];
    assert_eq!(1, crate::q16::from_bits(bytes).leading_run());
    assert_eq!(1, crate::q32::NAR.leading_run());
  }

  #[test]
  fn leading_run_27() {
    let bytes = [
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0b00010111,0b00000000,0b00000000,0b00000000,
    ];
    assert_eq!(27, crate::q16::from_bits(bytes).leading_run());
    let bytes = [
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
      0x00,0x11,0x22,0x33,0b11100111,0b11111111,0b11111111,0b11111111,
    ];
    assert_eq!(27, crate::q16::from_bits(bytes).leading_run());
  }

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
