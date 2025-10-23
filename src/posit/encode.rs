use super::*;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Decoded<N, ES, Int> {
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
  ///
  /// # Safety
  ///
  /// [`self.is_normalised()`](Self::is_normalised) has to hold, or calling this function
  /// is *undefined behaviour*.
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
    // The maximum regime length is `Self::BITS - 3` in the case of a run of 0s, and 
    // `Self::BITS - 2` in the case of a run of 1s. Respectively, the maximum `regime_raw` is thus 
    // `Self::BITS - 2` and `Self::BITS - 1` in the case of a run of 0s and of a run of 1s.
    //
    //   - Maximum regime of 0s: s000…001
    //   - Maximum regime of 1s: s111…111
    //
    // We can, however, clamp always the `regime_raw` to `Self::BITS - 3`, and simply set the lsb
    // to 1 whenever the `regime_raw` would exceed that value, since both the cases above end in
    // 1. This way we posit consists entirely of regime bits (plus the sign bit). In this case, we
    // return early, and the rest of the code can assume `regime_raw < Self::BITS - 2`.
    let regime_raw_max = Self::BITS - 3;
    let regime_overflow = regime_raw > regime_raw_max;
    let regime_raw = if regime_overflow {regime_raw_max} else {regime_raw};

    // Continue assembling the regime bits.
    let regime_bits = (!frac_xor_regime).mask_msb(2) >> regime_raw;
    // Combine the sign and regime bits into a register. The msb of the result, i.e. the sign bit,
    // is the msb of `frac`.
    let sign_and_regime_bits = self.frac.mask_msb(1) | regime_bits.lshr(1);
    let sign_and_regime_bits = sign_and_regime_bits >> Self::JUNK_BITS;

    // Next we need to place the exponent bits in the right place, just after the regime bits. The
    // sign and regime take up: 1 bit (sign) + regime_raw + 1 bits (run of 0s/1s) + 1 bit
    // (regime terminating 1/0). Exponent bits go this amount of bits from the left. The fraction
    // bits (sans the hidden bits of course) go immediately after that.
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
    // just before the |) `odd`, the first bit afterwards `round`, and the remaining bits
    // `sticky`. In terms of these, we have
    //
    //   odd | round | sticky | result
    //   ..x | 0     |  x     | round down (+0)
    //   ..0 | 1     | =0     | round down to even (+0)
    //   ..1 | 1     | =0     | round up to even (+1)
    //   ..x | 1     | ≠0     | round up (+1)
    //
    // So this means that if we keep track of these three things, that is: (1) set `round` equal to
    // the leftmost of all the shifted out bits, (2) accumulate into `sticky` all the rest of the
    // shifted out bits, and (3) set `odd` to the lsb of the unrounded result, we have a boolean
    // formula
    //
    //   round & (odd | (sticky != 0))
    //
    // that tells us whether to round down (0) or up (+1).

    // Okay! So let's assemble the `sign_and_regime_bits` and `exponent_and_fraction_bits` into
    // `all_bits`, while accumulating all but the last shifted out bits to `sticky`, and the last
    // shifted out bit to `round`.

    // If Self::ES > 2, then we lost some bits of fraction already (see `fraction_bits`). If there
    // are JUNK_BITS, likewise (see `exponent_and_fraction_bits`).
    if const { Self::JUNK_BITS + Self::ES > 2 } {
      sticky |= self.frac.mask_lsb(Self::JUNK_BITS + Self::ES - 2);
    };
    // Now remember, like we said, the lowest `regime_raw + 3` bits (1 sign bit, `regime_raw + 1`
    // run of 0s or 1s, 1 terminating bit) of `exponent_and_fraction_bits` are shifted out.
    //
    // Example:
    //
    //   regime_raw+3 = 6
    //   sign_and_regime_bits               = 0b100001_000000…
    //   exponent_and_fraction_bits         = 0b11010010100011
    //   exponent_and_fraction_bits.lshr(6) = 0b…00000_1101001
    //
    // The lowest `regime_raw + 2` bits of `exponent_and_fraction_bits` go to `sticky`, and the
    // last one shifted out goes to `round`.
    sticky |= exponent_and_fraction_bits.mask_lsb(2 + regime_raw);
    let exponent_and_fraction_bits = exponent_and_fraction_bits.lshr(2 + regime_raw);
    let round = exponent_and_fraction_bits.get_lsb();
    let exponent_and_fraction_bits = exponent_and_fraction_bits.lshr(1);

    // Assemble the bits of the (unrounded) result; the lowest determines whether it is odd, and
    // thus we can compute the formula above to decide whether we need to round up.
    let all_bits = sign_and_regime_bits | exponent_and_fraction_bits;  // TODO problematic data dependency
    let odd = all_bits.get_lsb();

    let round_up: bool = round & (odd | (sticky != Int::ZERO));

    // Assemble the final result, and return
    let bits = all_bits + Int::from(round_up & !regime_overflow);
    unsafe { Posit::from_bits_unchecked(bits | Int::from(regime_overflow)) }
  }

  /// Encode a posit, **ignoring rounding**.
  ///
  /// This function is suitable for encoding a [`Decoded`] that was obtained from
  /// [`Posit::decode_regular`], or that was otherwise crafted as a valid Posit. If if might need
  /// rounding (for instance, if you obtained it from doing an arithmetic operation), see
  /// [`Self::encode_regular_round`].
  ///
  /// # Safety
  ///
  /// [`self.is_normalised()`](Self::is_normalised) has to hold, or calling this function
  /// is *undefined behaviour*.
  #[inline]
  pub(crate) unsafe fn encode_regular(self) -> Posit<N, ES, Int> {
    debug_assert!(
      self.is_normalised(),
      "Safety precondition violated: {:?} cannot have an underflowing frac or overflowing exp", self,
    );
    // TODO: bench vs specialised impl
    unsafe { self.encode_regular_round(Int::ZERO) }
  }

  /// Encode a posit, rounding if necessary. The core logic lives in [Self::encode_regular_round].
  ///
  /// If `!self.is_normalised()`, return `Err(())` instead.
  #[cfg(test)]
  pub(crate) fn try_encode_round(self, sticky: Int) -> Result<Posit<N, ES, Int>, ()> {
    if self.is_normalised() {
      Ok(unsafe { self.encode_regular_round(sticky) })
    } else {
      Err(())
    }
  }

  /// Encode a posit, **ignoring rounding**. The core logic lives in [Self::encode_regular].
  ///
  /// If `!self.is_normalised()`, return `Err(())` instead.
  #[cfg(test)]
  pub(crate) fn try_encode(self) -> Result<Posit<N, ES, Int>, ()> {
    if self.is_normalised() {
      Ok(unsafe { self.encode_regular() })
    } else {
      Err(())
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use malachite::rational::Rational;
  use proptest::prelude::*;
  use super::test::posit_6_2;

  mod roundtrip {
    use super::*;

    #[test]
    fn posit_6_2_manual() {
      for (posit, _) in posit_6_2() {
        assert_eq!(unsafe { posit.decode_regular().encode_regular() }, posit)
      }
    }

    macro_rules! test_exhaustive {
      ($name:ident, $posit:ty) => {
        #[test]
        fn $name() {
          for p in <$posit>::cases_exhaustive() {
            assert_eq!(p.try_decode().expect("Invalid test case!").try_encode(), Ok(p))
          }
        }
      }
    }

    macro_rules! test_proptest {
      ($name:ident, $posit:ty) => {
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]
          #[test]
          fn $name(p in <$posit>::cases_proptest()) {
            assert_eq!(p.try_decode().expect("Invalid test case!").try_encode(), Ok(p))
          }
        }
      }
    }

    test_exhaustive!{posit_10_0_exhaustive, Posit::<10, 0, i16>}
    test_exhaustive!{posit_10_1_exhaustive, Posit::<10, 1, i16>}
    test_exhaustive!{posit_10_2_exhaustive, Posit::<10, 2, i16>}
    test_exhaustive!{posit_10_3_exhaustive, Posit::<10, 3, i16>}

    test_exhaustive!{posit_8_0_exhaustive, Posit::<8, 0, i8>}
    test_exhaustive!{posit_20_4_exhaustive, Posit::<20, 4, i32>}

    test_exhaustive!{p8_exhaustive, crate::p8}
    test_exhaustive!{p16_exhaustive, crate::p16}
    test_proptest!{p32_proptest, crate::p32}
    test_proptest!{p64_proptest, crate::p64}

    test_exhaustive!{posit_3_0_exhaustive, Posit::<3, 0, i8>}
    test_exhaustive!{posit_4_0_exhaustive, Posit::<4, 0, i8>}
    test_exhaustive!{posit_4_1_exhaustive, Posit::<4, 1, i8>}
  }

  mod rounding {
    use super::*;

    /// Aux function: assert that `decoded` is indeed `rational`, and that it is encoded
    /// (after rounding) into `posit`.
    fn assert_encode_rounded<const N: u32, const ES: u32, Int: crate::Int>(
      rational: &str,
      decoded: Decoded<N, ES, Int>,
      posit: Int,
    ) where Rational: From<Decoded<N, ES, Int>> {
      use core::str::FromStr;
      assert_eq!(Rational::from(decoded), Rational::from_str(rational).unwrap());
      assert_eq!(decoded.try_encode(), Ok(Posit::<N, ES, Int>::from_bits(posit)));
    }

    #[test]
    #[allow(overflowing_literals)]
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
    #[allow(overflowing_literals)]
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
    #[allow(overflowing_literals)]
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
    #[allow(overflowing_literals)]
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
    fn is_correct_rounded<const N: u32, const ES: u32, Int: crate::Int>(
      decoded: Decoded<N, ES, Int>,
      sticky: bool,
    ) -> bool
    where
      Rational: From<Decoded<N, ES, Int>>,
      Rational: TryFrom<Posit<N, ES, Int>, Error = super::rational::IsNaR>,
    {
      use malachite::base::num::arithmetic::traits::Pow;
      let epsilon = Rational::try_from(Posit::<N, ES, Int>::MIN_POSITIVE).unwrap().pow(32i64);
      let posit = decoded.try_encode_round(Int::from(sticky)).expect("Invalid test case!");
      let exact = if !sticky {Rational::from(decoded)} else {Rational::from(decoded) + epsilon};
      super::rational::is_correct_rounded(exact, posit)
    }

    macro_rules! test_exhaustive {
      ($name:ident, $decoded:ty) => {
        #[test]
        fn $name() {
          for d in <$decoded>::cases_exhaustive() {
            for s in [false, true] {
              assert!(is_correct_rounded(d, s), "decoded={:?} sticky={:?}", d, s)
            }
          }
        }
      }
    }

    macro_rules! test_proptest {
      ($name:ident, $decoded:ty) => {
        proptest!{
          #![proptest_config(ProptestConfig::with_cases(4 * crate::PROPTEST_CASES))]
          #[test]
          fn $name(d in <$decoded>::cases_proptest(), s: bool) {
            assert!(is_correct_rounded(d, s), "decoded={:?} sticky={:?}", d, s)
          }
        }
      }
    }

    test_exhaustive!{posit_10_0_exhaustive, Decoded::<10, 0, i16>}
    test_exhaustive!{posit_10_1_exhaustive, Decoded::<10, 1, i16>}
    test_exhaustive!{posit_10_2_exhaustive, Decoded::<10, 2, i16>}
    test_exhaustive!{posit_10_3_exhaustive, Decoded::<10, 3, i16>}

    test_exhaustive!{posit_8_0_exhaustive, Decoded::<8, 0, i8>}
    test_proptest!{posit_20_4_proptest, Decoded::<20, 4, i32>}

    test_exhaustive!{p8_exhaustive, Decoded::<8, 2, i8>}
    test_exhaustive!{p16_exhaustive, Decoded::<16, 2, i16>}
    test_proptest!{p32_proptest, Decoded::<32, 2, i32>}
    test_proptest!{p64_proptest, Decoded::<64, 2, i64>}

    test_exhaustive!{posit_3_0_exhaustive, Decoded::<3, 0, i8>}
    test_exhaustive!{posit_4_0_exhaustive, Decoded::<4, 0, i8>}
    test_exhaustive!{posit_4_1_exhaustive, Decoded::<4, 1, i8>}

    #[test]
    fn p8_max() {
      type P = Posit<8, 2, i16>;
      assert_eq!(
        P::MAX.try_decode(),
        Ok(Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^24
          exp: 24,
        }),
      );

      assert_eq!(
        Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^25
          exp: 25,
        }.try_encode(),
        Ok(P::MAX),
      );
      assert_eq!(
        Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^26
          exp: 26,
        }.try_encode(),
        Ok(P::MAX),
      );
      assert_eq!(
        Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^53
          exp: 53,
        }.try_encode(),
        Ok(P::MAX),
      );
      assert_eq!(
        Decoded {
          frac: 0b01_111001 << 8,  // -1.890625 × 2^24
          exp: 24,
        }.try_encode(),
        Ok(P::MAX),
      );
    }

    #[test]
    fn p8_min() {
      type P = Posit<8, 2, i16>;
      assert_eq!(
        P::MIN.try_decode(),
        Ok(Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^24
          exp: 23,
        }),
      );

      assert_eq!(
        Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^25
          exp: 24,
        }.try_encode(),
        Ok(P::MIN),
      );
      assert_eq!(
        Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^26
          exp: 25,
        }.try_encode(),
        Ok(P::MIN),
      );
      assert_eq!(
        Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^54
          exp: 53,
        }.try_encode(),
        Ok(P::MIN),
      );
      assert_eq!(
        Decoded {
          frac: 0b10_111001 << 8,  // -1.109375 × 2^24
          exp: 24,
        }.try_encode(),
        Ok(P::MIN),
      );
    }

    #[test]
    fn p8_min_positive() {
      type P = Posit<8, 2, i16>;
      assert_eq!(
        P::MIN_POSITIVE.try_decode(),
        Ok(Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^-24
          exp: -24,
        }),
      );

      assert_eq!(
        Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^-25
          exp: -25,
        }.try_encode(),
        Ok(P::MIN_POSITIVE),
      );
      assert_eq!(
        Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^-26
          exp: -26,
        }.try_encode(),
        Ok(P::MIN_POSITIVE),
      );
      assert_eq!(
        Decoded {
          frac: 0b01_000000 << 8,  // 1 × 2^-54
          exp: -54,
        }.try_encode(),
        Ok(P::MIN_POSITIVE),
      );
      assert_eq!(
        Decoded {
          frac: 0b01_111001 << 8,  // -1.890625/2 × 2^-24
          exp: -24 - 1,
        }.try_encode(),
        Ok(P::MIN_POSITIVE),
      );
    }

    #[test]
    fn p8_max_negative() {
      type P = Posit<8, 2, i16>;
      assert_eq!(
        P::MAX_NEGATIVE.try_decode(),
        Ok(Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^-24
          exp: -25,
        }),
      );

      assert_eq!(
        Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^-25
          exp: -26,
        }.try_encode(),
        Ok(P::MAX_NEGATIVE),
      );
      assert_eq!(
        Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^-26
          exp: -27,
        }.try_encode(),
        Ok(P::MAX_NEGATIVE),
      );
      assert_eq!(
        Decoded {
          frac: 0b10_000000 << 8,  // -1 × 2^-53
          exp: -54,
        }.try_encode(),
        Ok(P::MAX_NEGATIVE),
      );
      assert_eq!(
        Decoded {
          frac: 0b10_111001 << 8,  // -1.109375/2 × 2^-24
          exp: -25 - 1,
        }.try_encode(),
        Ok(P::MAX_NEGATIVE),
      );
    }
  }
}
