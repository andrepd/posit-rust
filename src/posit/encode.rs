use super::*;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Decoded<N, ES, Int> {
  /// Aux function, for debug prints
  fn bin(x: Int) -> Posit<N, ES, Int> { Posit(x) }

  const JUNK_BITS: u32 = Posit::<N, ES, Int>::JUNK_BITS;

  /// Encode a posit, rounding if necessary. The core logic lives in [Self::encode_regular_round].
  pub(crate) fn try_encode_round(self, sticky: Int) -> Option<Posit<N, ES, Int>> {
    if self.is_normalised() {
      Some(unsafe { self.encode_regular_round(sticky) })
    } else {
      None
    }
  }

  /// Encode a posit, rounding if necessary. The rounding rule is always the same: "round to
  /// nearest, round ties to even bit pattern, never round to 0 (i.e. never over- or under-flow)".
  ///
  /// `sticky` is the sticky bit: it is `Int::ZERO` **if and only if** all of the lost bits were 0.
  /// In other words, accumulate any lost bits to `sticky`, then pass it to `encode_regular_round`
  /// to get a correctly rounded Posit.
  ///
  /// This function is suitable for encoding a [`Decoded`] that might need rounding to produce a
  /// valid Posit (for example, if it was obtained from doing an arithmetic operation). If you
  /// don't need to round, see [`Self::encode_regular`].
  pub(crate) unsafe fn encode_regular_round(self, mut sticky: Int) -> Posit<N, ES, Int> {
    debug_assert!(
      self.is_normalised(),
      "Safety precondition violated: {:?} cannot have an underflowing frac or overflowing exp", self,
    );

    // Start by extracting the regime part of the exponent (bits higher than the lowest ES).
    let regime = self.exp >> ES;

    // For the regime bits, we want to create the following bits (let n be the value of `regime`
    // and s be the `sign` of the overall posit):
    //
    //   A run of -n  0s followed by a 1, if n is negative and s is positive
    //   A run of n+1 1s followed by a 0, if n is positive and s is positive
    //
    // and the reverse if the sign is negative (remember the fields are interpreted after we take
    // the two's complement of the bit pattern)
    //
    //   A run of -n  1s followed by a 0, if n is negative and s is negative
    //   A run of n+1 0s followed by a 1, if n is positive and s is negative
    //
    // We can reformulate this in two ways: (1) we can again note that `-n = !n + 1`, and (2) also
    // condense the "n is positive/negative" and "s is positive/negative" conditions using the xor
    // of n and s, yielding
    //
    //   A run of !n+1 0s followed by a 1, if n ^ s is negative
    //   A run of  n+1 1s followed by a 0, if n ^ s is positive
    //
    // Great! But how do we build the bit pattern?
    //
    // Now note the following: the two msb of regime are always 11 or 00, since the regime is never
    // bigger than ±Int::BITS, and is represented in a value with the same number of bits (e.g.
    // never more than the number ±64 represented in an i64). Note also that the two msb of frac
    // are always 10 or 01.
    //
    // Therefore, if `n ^ s` is positive, its two msb will be 01, and if it is negative, its two
    // msb will be 10. So just negate them, and this is precisely what we want! We just need
    // to "pull" them to the right by `regime_raw`, where `regime_raw` is n if n is positive, or
    // `!n` if n is negative (a sort of "absolute value" but with logical not `!` instead of
    // arithmetic negation `-`; cf. the comments in `decode_regular`).
    //
    // Example:
    //   regime         = 3
    //   sign           = 0b01...
    //   !(regime^sign) = 0b10...
    //   regime_raw     = 3
    //   !(regime^sign) >> regime_raw = 0b11110...  (4 1s followed by a 0 = regime 4-1, correct)
    //
    // Example:
    //   regime         = -3
    //   sign           = 0b01...
    //   !(regime^sign) = 0b01...
    //   regime_raw     = 2
    //   !(regime^sign) >> regime_raw = 0b0001....  (3 0s followed by a 1 = regime -3, correct)
    //
    // Example:
    //   regime         = 3
    //   sign           = 0b10...
    //   !(regime^sign) = 0b01...
    //   regime_raw     = 3
    //   !(regime^sign) >> regime_raw = 0b00001...  (4 0s followed by a 1 = regime !(-4), correct)
    //
    // We can now assemble the whole thing
    let frac_xor_regime = self.frac ^ self.exp;
    let regime_raw = regime.not_if_negative(regime).as_u32();

    // A corner case, before we proceed: posit rounding rules state that, for a positive number,
    // any number > MAX is rounded to MAX, and any number < MIN_POSITIVE is rounded to
    // MIN_POSITIVE, and conversely for negative numbers, any number < MIN is rounded to MIN, and
    // any number > MAX_NEGATIVE is rounded to MAX_NEGATIVE. I.e. we **never** round to 0 or to
    // NaR.
    //
    // Equivalently, this means that we have to clamp the exponent to the representable range. But
    // also equivalently, it suffices to clamp the regime *length* to the maximum regime length
    // allowed. This is enough to clamp the exponent to be no greater than the maximum exponent
    // and no smaller than the maximum exponent.
    //
    // The maximum regime length is `Self::BITS - 3`, thus is `regime_raw >= Self::BITS - 2`, the
    // posit consists entirely of regime bits (plus the sign bit). In this case, we return early,
    // and the rest of the code can assume `regime_raw < Self::BITS - 2`.
    let regime_raw_max = Self::BITS - 2;
    if regime_raw >= regime_raw_max {  // TODO mark unlikely?
      // See the code outside this branch for an explanation.
      let regime_bits = (!frac_xor_regime).mask_msb(2) >> regime_raw_max;
      let sign_and_regime_bits = self.frac.mask_msb(1) | regime_bits.lshr(1);
      let sign_and_regime_bits = sign_and_regime_bits >> Self::JUNK_BITS;
      return unsafe { Posit::from_bits_unchecked(sign_and_regime_bits | Int::ONE) }
    }

    // Continue assembling the regime bits.
    let regime_bits = (!frac_xor_regime).mask_msb(2) >> regime_raw;
    // Combine the sign and regime bits into a register. The msb of the result, i.e. the sign bit,
    // is the msb of `frac`.
    let sign_and_regime_bits = self.frac.mask_msb(1) | regime_bits.lshr(1);
    let sign_and_regime_bits = sign_and_regime_bits >> Self::JUNK_BITS;

    // Next we need to place the exponent bits in the right place, just after the regime bits. This
    // is in total 1 bit (sign) + regime_raw + 1 bits (run of 0s/1s) + 1 bit (regime terminating
    // 1/0); exponent bits go this amount of bits from the left. The fraction bits (sans the
    // hidden bits) go immediately after that.
    //
    // To do this, we will first assemble the exponent and fraction bits in a register, then shift
    // them to the right place (saves 1/2 instructions and—more importantly—makes rounding
    // calculations easier, compared to shifting them separately).
    //
    // Just one thing to remember: that if the posit is negative, these exponent bits have to be
    // negated as well.
    let exponent_bits = if const { ES != 0 } {self.exp.not_if_negative(self.frac) << (Int::BITS - ES)} else {Int::ZERO};
    let fraction_bits = (self.frac << 2).lshr(Self::ES);
    let exponent_and_fraction_bits = exponent_bits | fraction_bits;
    let exponent_and_fraction_bits = exponent_and_fraction_bits.lshr(Self::JUNK_BITS);

    // Now comes a tricky part: the rounding. The rounding rules translate to a very simple rule in
    // terms of bit patterns: just "represent as an infinite-precision bit string, then round to
    // nearest, if tied round to even bit pattern".
    //
    // Some examples: let's say we have a bit string that we want to round at the |
    //
    //   0b010101|011011 -> round to nearest = down    -> 0b010101
    //   0b010101|111011 -> round to nearest = up      -> 0b010110
    //   0b010101|100000 -> tied, round to even = up   -> 0b010110
    //   0b010100|100000 -> tied, round to even = down -> 0b010100
    //
    // How do we achieve this in practice? Let's call the lsb of the bits we want to keep (the bit
    // just before the |) `even`, the first bit afterwards `round`, and the remaining bits
    // `sticky`. In terms of these, we have
    //
    //   even | round | sticky | result
    //   ...x | 0     |  x     | round down (+0)
    //   ...0 | 1     | =0     | round down to even (+0)
    //   ...1 | 1     | =0     | round up to even (+1)
    //   ...x | 1     | ≠1     | round up (+1)
    //
    // So this means that if we keep track of these three things, that is: (1) set `round` equal to
    // the leftmost of all the shifted out bits, (2) accumulate into `sticky` all the rest of the
    // shifted out bits, and (3) set `even` to the lsb of the unrounded result, we have a boolean
    // formula
    //
    //   round & (even | (sticky != 0))
    //
    // that tells us whether to round down (0) or up (+1).

    // If Self::ES > 2, then we lost some bits of fraction already (see `fraction_bits`). If there
    // are JUNK_BITS, likewise (see `exponent_and_fraction_bits`).
    if const { Self::JUNK_BITS + Self::ES > 2 } {
      sticky |= self.frac.mask_lsb(Self::JUNK_BITS + Self::ES - 2);
    };
    // There is at least 3 bits we shift out (srr, 1 sign bit and 2 regime bits, is the shortest
    // thing possible before the exponent_and_fraction_bits). Accumulate 2 onto sticky and shift 2
    // out.
    sticky |= exponent_and_fraction_bits.mask_lsb(2);
    let exponent_and_fraction_bits = exponent_and_fraction_bits.lshr(2);
    // Now remember, we need to shift out exponent_and_fraction_bits in total by `regime_raw + 3`
    // bits, the lowest `regime_raw + 2` of which need to be accumulated to `sticky`, and the last
    // one to `round`. We have already shifted 2 bits to sticky, so we need to shift `regime_raw`
    // more bits there,
    sticky |= exponent_and_fraction_bits.mask_lsb(regime_raw);
    // and the bit afterwards to sticky,
    let exponent_and_fraction_bits = exponent_and_fraction_bits.lshr(regime_raw);
    let round = exponent_and_fraction_bits.get_lsb();
    // and the bit after that (i.e. the lowest bit actually in the final result), tells us whether
    // the unrounded bit pattern is even.
    let exponent_and_fraction_bits = exponent_and_fraction_bits.lshr(1);
    let mut even = exponent_and_fraction_bits.get_lsb();
    // But if we shift the *whole thing* out, then the even bit is actually the lsb of regime_bits
    if regime_raw >= Self::BITS - 3 { even = sign_and_regime_bits.get_lsb() }  // TODO find better way of doing this + clamping exp (= clamping regime_raw)
    // Finally, we have the result of whether we need to round or not
    let round_up: bool = round & (even | (sticky != Int::ZERO));

    // Assemble the final result, and return
    let bits =
      sign_and_regime_bits
      + exponent_and_fraction_bits
      + Int::from(round_up);
    unsafe { Posit::from_bits_unchecked(bits) }
  }

  /// Encode a posit, **ignoring rounding**. The core logic lives in [Self::encode_regular].
  pub(crate) fn try_encode(self) -> Option<Posit<N, ES, Int>> {
    if self.is_normalised() {
      Some(unsafe { self.encode_regular() })
    } else {
      None
    }
  }

  /// Encode a posit, **ignoring rounding**.
  ///
  /// This function is suitable for encoding a [`Decoded`] that was obtained from
  /// [`Posit::decode_regular`], or that was otherwise crafted as a valid Posit. If if might need
  /// rounding (for instance, if you obtained it from doing an arithmetic operation), see
  /// [`Self::encode_regular_round`].
  #[inline]
  pub(crate) unsafe fn encode_regular(self) -> Posit<N, ES, Int> {
    debug_assert!(
      self.is_normalised(),
      "Safety precondition violated: {:?} cannot have an underflowing frac or overflowing exp", self,
    );
    // TODO: bench vs specialised impl
    unsafe { self.encode_regular_round(Int::ZERO) }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use malachite::rational::Rational;
  use proptest::prelude::*;
  use super::test::posit_6_2;
  use super::decode::TryDecoded;

  mod roundtrip {
    use super::*;

    #[test]
    fn posit_6_2_manual() {
      for (posit, _) in posit_6_2() {
        assert_eq!(unsafe { posit.decode_regular().encode_regular() }, posit)
      }
    }

    fn assert_roundtrip<const N: u32, const ES: u32, Int: crate::Int>(p: Posit<N, ES, Int>) {
      let super::decode::TryDecoded::Regular(decoded) = p.try_decode() else { panic!("Invalid test case") };
      assert_eq!(decoded.try_encode(), Some(p))
    }

    #[test]
    fn posit_10_0_exhaustive() {
      for p in Posit::<10, 0, i16>::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }

    #[test]
    fn posit_10_1_exhaustive() {
      for p in Posit::<10, 1, i16>::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }

    #[test]
    fn posit_10_2_exhaustive() {
      for p in Posit::<10, 2, i16>::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }

    #[test]
    fn posit_10_3_exhaustive() {
      for p in Posit::<10, 3, i16>::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }

    #[test]
    fn posit_8_0_exhaustive() {
      for p in Posit::<8, 0, i8>::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }

    #[test]
    fn p8_exhaustive() {
      for p in crate::p8::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }

    #[test]
    fn p16_exhaustive() {
      for p in crate::p16::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }

    const PROPTEST_CASES: u32 = if cfg!(debug_assertions) {0x1_0000} else {0x80_0000};
    proptest!{
      #![proptest_config(ProptestConfig::with_cases(PROPTEST_CASES))]

      #[test]
      fn p32_proptest(p in crate::p32::cases_proptest()) {
        assert_roundtrip(p)
      }

      #[test]
      fn p64_proptest(p in crate::p64::cases_proptest()) {
        assert_roundtrip(p)
      }
    }

    #[test]
    fn posit_20_4_exhaustive() {
      for p in Posit::<20, 4, i32>::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }

    #[test]
    fn posit_3_0_exhaustive() {
      for p in Posit::<3, 0, i8>::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }

    #[test]
    fn posit_4_0_exhaustive() {
      for p in Posit::<4, 0, i8>::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }

    #[test]
    fn posit_4_1_exhaustive() {
      for p in Posit::<4, 1, i8>::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }
  }

  mod rounding {
    use super::*;

    /// Aux function: assert that `decoded` is indeed `rational`, and that it is encoded
    /// (after rounding) into `posit`.
    fn assert_encode_rounded<const N: u32, const ES: u32, Int: crate::Int>(
      rational: &str,
      decoded: Decoded<N, ES, Int>,
      posit: Int::Unsigned,
    ) where Rational: From<Decoded<N, ES, Int>>,  {
      use core::str::FromStr;
      assert_eq!(Rational::from(decoded), Rational::from_str(rational).unwrap());
      assert_eq!(decoded.try_encode(), Some(Posit::<N, ES, Int>::from_bits_unsigned(posit)));
    }

    #[test]
    fn posit_6_2_manual_pos() {
      type D = Decoded<6, 2, i8>;
      assert_encode_rounded("200/100", D { frac: 0b01_0000 << 2, exp: 1 }, 0b010010);  // 2    → 2
      assert_encode_rounded("225/100", D { frac: 0b01_0010 << 2, exp: 1 }, 0b010010);  // 2.25 → 2
      assert_encode_rounded("250/100", D { frac: 0b01_0100 << 2, exp: 1 }, 0b010010);  // 2.5  → 2
      assert_encode_rounded("275/100", D { frac: 0b01_0110 << 2, exp: 1 }, 0b010011);  // 2.75 → 3
      assert_encode_rounded("300/100", D { frac: 0b01_1000 << 2, exp: 1 }, 0b010011);  // 3    → 3
      assert_encode_rounded("325/100", D { frac: 0b01_1010 << 2, exp: 1 }, 0b010011);  // 3.25 → 3
      assert_encode_rounded("350/100", D { frac: 0b01_1100 << 2, exp: 1 }, 0b010100);  // 3.5  → 4
      assert_encode_rounded("375/100", D { frac: 0b01_1110 << 2, exp: 1 }, 0b010100);  // 3.75 → 4
      assert_encode_rounded("400/100", D { frac: 0b01_0000 << 2, exp: 2 }, 0b010100);  // 4    → 4
    }

    #[test]
    fn posit_6_2_manual_neg() {
      type D = Decoded<6, 2, i8>;
      assert_encode_rounded("-200/100", D { frac: 0b10_0000 << 2, exp: 0 }, 0b101110);  // -2    → -2
      assert_encode_rounded("-225/100", D { frac: 0b10_1110 << 2, exp: 1 }, 0b101110);  // -2.25 → -2
      assert_encode_rounded("-250/100", D { frac: 0b10_1100 << 2, exp: 1 }, 0b101110);  // -2.5  → -2
      assert_encode_rounded("-275/100", D { frac: 0b10_1010 << 2, exp: 1 }, 0b101101);  // -2.75 → -3
      assert_encode_rounded("-300/100", D { frac: 0b10_1000 << 2, exp: 1 }, 0b101101);  // -3    → -3
      assert_encode_rounded("-325/100", D { frac: 0b10_0110 << 2, exp: 1 }, 0b101101);  // -3.25 → -3
      assert_encode_rounded("-350/100", D { frac: 0b10_0100 << 2, exp: 1 }, 0b101100);  // -3.5  → -4
      assert_encode_rounded("-375/100", D { frac: 0b10_0010 << 2, exp: 1 }, 0b101100);  // -3.75 → -4
      assert_encode_rounded("-400/100", D { frac: 0b10_0000 << 2, exp: 1 }, 0b101100);  // -4    → -4
    }

    #[test]
    fn p8_manual_pos() {
      type D = Decoded<8, 2, i8>;
      assert_encode_rounded("900/100",  D { frac: 0b01_001000, exp: 3 }, 0b01011001);  // 9     → 9
      assert_encode_rounded("925/100",  D { frac: 0b01_001010, exp: 3 }, 0b01011001);  // 9.25  → 9
      assert_encode_rounded("950/100",  D { frac: 0b01_001100, exp: 3 }, 0b01011010);  // 9.5   → 10
      assert_encode_rounded("975/100",  D { frac: 0b01_001110, exp: 3 }, 0b01011010);  // 9.75  → 10
      assert_encode_rounded("1000/100", D { frac: 0b01_010000, exp: 3 }, 0b01011010);  // 10    → 10
      assert_encode_rounded("1025/100", D { frac: 0b01_010010, exp: 3 }, 0b01011010);  // 10.25 → 10
      assert_encode_rounded("1050/100", D { frac: 0b01_010100, exp: 3 }, 0b01011010);  // 10.5  → 10
      assert_encode_rounded("1075/100", D { frac: 0b01_010110, exp: 3 }, 0b01011011);  // 10.75 → 11
      assert_encode_rounded("1100/100", D { frac: 0b01_011000, exp: 3 }, 0b01011011);  // 11    → 11
    }

    #[test]
    fn p8_manual_neg() {
      type D = Decoded<8, 2, i8>;
      assert_encode_rounded("-900/100",  D { frac: 0b10_111000u8 as _, exp: 3 }, 0b10100111);  // -9     → -9
      assert_encode_rounded("-925/100",  D { frac: 0b10_110110u8 as _, exp: 3 }, 0b10100111);  // -9.25  → -9
      assert_encode_rounded("-950/100",  D { frac: 0b10_110100u8 as _, exp: 3 }, 0b10100110);  // -9.5   → -10
      assert_encode_rounded("-975/100",  D { frac: 0b10_110010u8 as _, exp: 3 }, 0b10100110);  // -9.75  → -10
      assert_encode_rounded("-1000/100", D { frac: 0b10_110000u8 as _, exp: 3 }, 0b10100110);  // -10    → -10
      assert_encode_rounded("-1025/100", D { frac: 0b10_101110u8 as _, exp: 3 }, 0b10100110);  // -10.25 → -10
      assert_encode_rounded("-1050/100", D { frac: 0b10_101100u8 as _, exp: 3 }, 0b10100110);  // -10.5  → -10
      assert_encode_rounded("-1075/100", D { frac: 0b10_101010u8 as _, exp: 3 }, 0b10100101);  // -10.75 → -11
      assert_encode_rounded("-1100/100", D { frac: 0b10_101000u8 as _, exp: 3 }, 0b10100101);  // -11    → -11
    }

    /// Aux function: check that `decoded` is rounded correctly.
    fn is_correct_rounded<const N: u32, const ES: u32, Int: crate::Int>(decoded: Decoded<N, ES, Int>) -> bool
    where
      Rational: From<Decoded<N, ES, Int>> + TryFrom<Posit<N, ES, Int>>,
      <Rational as TryFrom<Posit<N, ES, Int>>>::Error: core::fmt::Debug
    {
      let posit = decoded.try_encode().expect("Invalid test case!");
      let exact = Rational::from(decoded);
      super::rational::is_correct_rounded(exact, posit)
    }

    #[test]
    fn posit_10_0_exhaustive() {
      for decoded in Decoded::<10, 0, i16>::cases_exhaustive() {
        assert!(is_correct_rounded(decoded), "{:?}: {:?}", decoded, decoded.try_encode())
      }
    }

    #[test]
    fn posit_10_1_exhaustive() {
      for decoded in Decoded::<10, 1, i16>::cases_exhaustive() {
        assert!(is_correct_rounded(decoded), "{:?}: {:?}", decoded, decoded.try_encode())
      }
    }

    #[test]
    fn posit_10_2_exhaustive() {
      for decoded in Decoded::<10, 2, i16>::cases_exhaustive() {
        assert!(is_correct_rounded(decoded), "{:?}: {:?}", decoded, decoded.try_encode())
      }
    }

    #[test]
    fn posit_10_3_exhaustive() {
      for decoded in Decoded::<10, 3, i16>::cases_exhaustive() {
        assert!(is_correct_rounded(decoded), "{:?}: {:?}", decoded, decoded.try_encode())
      }
    }

    #[test]
    fn posit_8_0_exhaustive() {
      for decoded in Decoded::<8, 0, i8>::cases_exhaustive() {
        assert!(is_correct_rounded(decoded), "{:?}: {:?}", decoded, decoded.try_encode())
      }
    }

    #[test]
    fn p8_exhaustive() {
      for decoded in Decoded::<8, 2, i8>::cases_exhaustive() {
        assert!(is_correct_rounded(decoded), "{:?}: {:?}", decoded, decoded.try_encode())
      }
    }

    #[test]
    fn p16_exhaustive() {
      for decoded in Decoded::<16, 2, i16>::cases_exhaustive() {
        assert!(is_correct_rounded(decoded), "{:?}: {:?}", decoded, decoded.try_encode())
      }
    }

    const PROPTEST_CASES: u32 = if cfg!(debug_assertions) {0x1_0000} else {0x80_0000};
    proptest!{
      #![proptest_config(ProptestConfig::with_cases(PROPTEST_CASES))]

      #[test]
      fn p32_proptest(decoded in Decoded::<32, 2, i32>::cases_proptest()) {
        assert!(is_correct_rounded(decoded), "{:?}: {:?}", decoded, decoded.try_encode())
      }

      #[test]
      fn p64_proptest(decoded in Decoded::<64, 2, i64>::cases_proptest()) {
        assert!(is_correct_rounded(decoded), "{:?}: {:?}", decoded, decoded.try_encode())
      }
    }

    #[test]
    fn posit_3_0_exhaustive() {
      for decoded in Decoded::<3, 0, i8>::cases_exhaustive() {
        assert!(is_correct_rounded(decoded), "{:?}: {:?}", decoded, decoded.try_encode())
      }
    }

    #[test]
    fn posit_4_0_exhaustive() {
      for decoded in Decoded::<4, 0, i8>::cases_exhaustive() {
        assert!(is_correct_rounded(decoded), "{:?}: {:?}", decoded, decoded.try_encode())
      }
    }

    #[test]
    fn posit_4_1_exhaustive() {
      for decoded in Decoded::<4, 1, i8>::cases_exhaustive() {
        assert!(is_correct_rounded(decoded), "{:?}: {:?}", decoded, decoded.try_encode())
      }
    }

    #[test]
    fn p8_max() {
      type P = Posit<8, 2, i16>;
      assert_eq!(
        P::MAX.try_decode(),
        TryDecoded::Regular(Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^24
          exp: 24,
        }),
      );

      assert_eq!(
        Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^25
          exp: 25,
        }.try_encode(),
        Some(P::MAX),
      );
      assert_eq!(
        Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^26
          exp: 26,
        }.try_encode(),
        Some(P::MAX),
      );
      assert_eq!(
        Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^53
          exp: 53,
        }.try_encode(),
        Some(P::MAX),
      );
      assert_eq!(
        Decoded {
          frac: 0b01_111001 << 8,  // -1.890625 × 2^24
          exp: 24,
        }.try_encode(),
        Some(P::MAX),
      );
    }

    #[test]
    fn p8_min() {
      type P = Posit<8, 2, i16>;
      assert_eq!(
        P::MIN.try_decode(),
        TryDecoded::Regular(Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^24
          exp: 23,
        }),
      );

      assert_eq!(
        Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^25
          exp: 24,
        }.try_encode(),
        Some(P::MIN),
      );
      assert_eq!(
        Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^26
          exp: 25,
        }.try_encode(),
        Some(P::MIN),
      );
      assert_eq!(
        Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^54
          exp: 53,
        }.try_encode(),
        Some(P::MIN),
      );
      assert_eq!(
        Decoded {
          frac: 0b10_111001 << 8,  // -1.109375 × 2^24
          exp: 24,
        }.try_encode(),
        Some(P::MIN),
      );
    }

    #[test]
    fn p8_min_positive() {
      type P = Posit<8, 2, i16>;
      assert_eq!(
        P::MIN_POSITIVE.try_decode(),
        TryDecoded::Regular(Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^-24
          exp: -24,
        }),
      );

      assert_eq!(
        Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^-25
          exp: -25,
        }.try_encode(),
        Some(P::MIN_POSITIVE),
      );
      assert_eq!(
        Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^-26
          exp: -26,
        }.try_encode(),
        Some(P::MIN_POSITIVE),
      );
      assert_eq!(
        Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^-54
          exp: -54,
        }.try_encode(),
        Some(P::MIN_POSITIVE),
      );
      assert_eq!(
        Decoded {
          frac: 0b01_111001 << 8,  // -1.890625/2 × 2^-24
          exp: -24 - 1,
        }.try_encode(),
        Some(P::MIN_POSITIVE),
      );
    }

    #[test]
    fn p8_max_negative() {
      type P = Posit<8, 2, i16>;
      assert_eq!(
        P::MAX_NEGATIVE.try_decode(),
        TryDecoded::Regular(Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^-24
          exp: -25,
        }),
      );

      assert_eq!(
        Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^-25
          exp: -26,
        }.try_encode(),
        Some(P::MAX_NEGATIVE),
      );
      assert_eq!(
        Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^-26
          exp: -27,
        }.try_encode(),
        Some(P::MAX_NEGATIVE),
      );
      assert_eq!(
        Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^-53
          exp: -54,
        }.try_encode(),
        Some(P::MAX_NEGATIVE),
      );
      assert_eq!(
        Decoded {
          frac: 0b10_111001 << 8,  // -1.109375/2 × 2^-24
          exp: -25 - 1,
        }.try_encode(),
        Some(P::MAX_NEGATIVE),
      );
    }
  }
}
