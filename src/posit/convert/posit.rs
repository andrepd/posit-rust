use super::*;
use crate::underlying::const_as;

impl<
  const N1: u32,
  const ES1: u32,
  Int1: crate::Int,
> Posit<N1, ES1, Int1> {
  /// Very fast, the `ES` have to be the same.
  fn round_from_fast<
    const N2: u32,
    const ES2: u32,
    Int2: crate::Int,
  >(self) -> Posit<N2, ES2, Int2> {
    if const { ES1 != ES2 } { unimplemented!() }
    if const { N1 <= N2 } {
      // Converting to a wider posit is even simpler: no rounding, just pad with zeroes.
      let bits = const_as::<Int1, Int2>(self.to_bits()) << (N2 - N1);
      // SAFETY: `bits` is a valid bit pattern for `N1`, so `bits << (N2 - N1)` must also be a
      // valid bit pattern for `N2` > `N1`.
      unsafe { Posit::from_bits_unchecked(bits) }
    } else {
      // Converting to a narrower posit is somewhat tricker: we may need to round, depending on
      // which bits were lost. The chopped off bits except the last (leftmost bit among those
      // chopped off) are stored in `sticky`, the last chopped bit is stored in the lsb of `round`.
      let sticky: Int2 = Int2::from(self.to_bits().mask_lsb(N1 - N2 - 1) != Int1::ZERO);
      let round: Int2 = const_as(self.to_bits() >> (N1 - N2 - 1));
      // Recall the rounding rule: "round to nearest, if tied round to even bit pattern".
      //
      //   bits | round | sticky | result
      //   ...x | 0     | x      | round down (+0)
      //   ...0 | 1     | 0      | round down to even (+0)
      //   ...1 | 1     | 0      | round up to even (+1)
      //   ...x | 1     | 1      | round up (+1)
      //
      // This results in the following boolean formula for determining whether to round up:
      //
      //   round & (bits | sticky)
      //
      let bits = const_as::<Int1, Int2>(self.to_bits() >> (N1 - N2));
      let round_up = round & (bits | sticky) & Int2::ONE;
      // But then again, we need to be careful of the following:
      //
      // - Not to round up from `0b1111…` to `0b0000…` or from `0b0111…` to `0b1000…`.
      // - Not to chop bits so that `0b000…1…` truncates to `0b0000…` and `0b100…1…` to `0b1000…`.
      //
      // Therefore: if the result is 0 or NaR, we have to "round up" if `sticky != 0`, and
      // to "round down" if there was a sign change in the bits.
      let is_special = Posit::<N2, ES2, Int2>::from_bits(bits).is_special();
      let round_up = round_up | ((round | sticky) & Int2::from(is_special));
      let bits_rounded = Posit::<N2, ES2, Int2>::sign_extend(bits.wrapping_add(round_up));
      let overflow = !(bits_rounded ^ bits).is_positive();
      Posit::from_bits(bits_rounded.wrapping_sub(Int2::from(overflow)))
    }
  }

  /// Slower, the `ES` may be different.
  fn round_from_slow<
    const N2: u32,
    const ES2: u32,
    Int2: crate::Int,
  >(self) -> Posit<N2, ES2, Int2> {
    if self == Self::ZERO {
      Posit::ZERO
    } else if self == Self::NAR {
      Posit::NAR
    } else {
      // SAFETY: `self` is not 0 or NaR
      let decoded = unsafe { self.decode_regular() };
      // Cast `frac` and `exp` to the target `Int2`; `frac` must also be shifted.
      let shift_right = if const { Int1::BITS <= Int2::BITS } {0} else {Int1::BITS - Int2::BITS};
      let shift_left = if const { Int1::BITS >= Int2::BITS } {0} else {Int2::BITS - Int1::BITS};
      let frac = const_as::<Int1, Int2>(decoded.frac >> shift_right) << shift_left;
      let exp = const_as::<Int1, Int2>(decoded.exp);
      // Lost bits, if any, must be collected into `sticky`.
      let sticky = Int2::from(decoded.frac.mask_lsb(shift_right) != Int1::ZERO);
      // Corner-case: if Self::MAX_EXP may overflow the destination type `Int2`, we must check
      // whether the exponent *does* overflow the destination type.
      if Int1::BITS > Int2::BITS
      && Self::MAX_EXP >= const_as(Decoded::<N2, ES2, Int2>::FRAC_DENOM)
      && decoded.exp.abs() >= const_as(Decoded::<N2, ES2, Int2>::FRAC_DENOM) {
        // TODO remove branch? It's exceedingly rare anyways
        let exp = Decoded::<N2, ES2, Int2>::FRAC_DENOM - Int2::ONE;
        let exp = if decoded.exp.is_positive() {exp} else {-exp};
        // SAFETY: `decoded.frac` starts with `0b01` or `0b10`, so `decoded.frac >> shift_right <<
        // shift_left` also does; `exp` is the max/min exponent.
        return unsafe { Decoded{frac, exp}.encode_regular() }
      }
      // SAFETY: `decoded.frac` starts with `0b01` or `0b10`, so `decoded.frac >> shift_right <<
      // shift_left` also does; `exp` is in bounds (if there is a risk of overflow, it's handled
      // above).
      unsafe { Decoded{frac, exp}.encode_regular_round(sticky) }
    }
  }
}

// Cannot impl RoundFrom trait because it conflicts with blanket impl... Has to be a function.
/*impl<
  const N1: u32,
  const ES1: u32,
  Int1: crate::Int,
  const N2: u32,
  const ES2: u32,
  Int2: crate::Int,
> RoundFrom<Posit<N1, ES1, Int1>> for Posit<N2, ES2, Int2>*/

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  /// Convert a posit into a different one, [rounding according to the standard].
  ///
  /// If the source and target types have the same ES (i.e. `ES == ES2`), such as is the case with
  /// the standard types, this is especially fast. This enables easy and seamless mixed-precision
  /// arithmetic.
  ///
  /// [rounding according to the standard]: https://posithub.org/docs/posit_standard-2.pdf#subsection.6.1
  ///
  /// # Examples
  ///
  /// ```
  /// # use fast_posit::{p8, p64, RoundFrom, RoundInto};
  /// let pi: p64 = core::f64::consts::PI.round_into();
  /// let two: p8 = 2.round_into();
  /// let tau: p64 = pi * two.convert();
  /// assert_eq!(tau, core::f64::consts::TAU.round_into())
  /// ```
  pub fn convert<
    const N2: u32,
    const ES2: u32,
    Int2: crate::Int,
  >(self) -> Posit<N2, ES2, Int2> {
    if const { ES == ES2 } {
      // If the two ES values are the same, converting posit values is incredibly simple: just
      // append 0s or truncate the bit pattern.
      self.round_from_fast()
    } else {
      // Otherwise, we need to decode and re-encode.
      self.round_from_slow()
    }
  }
}

#[cfg(test)]
#[allow(non_camel_case_types)]
mod tests {
  use super::*;
  use malachite::rational::Rational;
  use proptest::prelude::*;

  macro_rules! test_exhaustive {
    ($name: ident, $src:ty, $dst:ty) => {
      #[test]
      fn $name() {
        for src in <$src>::cases_exhaustive_all() {
          let dst: $dst = src.convert();
          assert!(super::rational::try_is_correct_rounded(Rational::try_from(src), dst))
        }
      }
    };
  }

  macro_rules! test_proptest {
    ($name: ident, $src:ty, $dst:ty) => {
      proptest!{
        #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
        #[test]
        fn $name(src in <$src>::cases_proptest_all()) {
          let dst: $dst = src.convert();
          assert!(super::rational::try_is_correct_rounded(Rational::try_from(src), dst))
        }
      }
    };
  }

  macro_rules! make_suite {
    ($macro_name: ident, $name_src:ident, $src:ty) => {
      mod $name_src {
        use super::*;
        $macro_name!{posit_10_0, $src, Posit<10, 0, i16>}
        $macro_name!{posit_10_1, $src, Posit<10, 1, i16>}
        $macro_name!{posit_10_2, $src, Posit<10, 2, i16>}
        $macro_name!{posit_10_3, $src, Posit<10, 3, i16>}
        $macro_name!{posit_8_0,  $src, Posit<8, 0, i8>}
        $macro_name!{posit_20_4, $src, Posit<20, 4, i32>}
        $macro_name!{p8,         $src, crate::p8}
        $macro_name!{p16,        $src, crate::p16}
        $macro_name!{p32,        $src, crate::p32}
        $macro_name!{p64,        $src, crate::p64}
        $macro_name!{posit_3_0,  $src, Posit<3, 0, i8>}
        $macro_name!{posit_4_0,  $src, Posit<4, 0, i8>}
        $macro_name!{posit_4_1,  $src, Posit<4, 1, i8>}
      }
    };
  }

  make_suite!{test_proptest, posit_10_0, Posit<10, 0, i16>}
  make_suite!{test_proptest, posit_10_1, Posit<10, 1, i16>}
  make_suite!{test_proptest, posit_10_2, Posit<10, 2, i16>}
  make_suite!{test_proptest, posit_10_3, Posit<10, 3, i16>}

  make_suite!{test_proptest, posit_8_0, Posit<8, 0, i8>}
  make_suite!{test_proptest, posit_20_4, Posit<20, 4, i32>}

  make_suite!{test_proptest, p8, crate::p8}
  make_suite!{test_proptest, p16, crate::p16}
  make_suite!{test_proptest, p32, crate::p32}
  make_suite!{test_proptest, p64, crate::p64}

  make_suite!{test_proptest, posit_3_0, Posit<3, 0, i8>}
  make_suite!{test_proptest, posit_4_0, Posit<4, 0, i8>}
  make_suite!{test_proptest, posit_4_1, Posit<4, 1, i8>}
}
