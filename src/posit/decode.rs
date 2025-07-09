use super::*;

#[derive(Debug)]
#[derive(PartialEq, Eq)]
pub enum TryDecoded<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> {
  Zero,
  NaR,
  Regular(Decoded<N, ES, Int>),
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  /// Decode a posit. The core logic lives in [Self::decode_regular].
  pub(crate) fn try_decode(self) -> TryDecoded<N, ES, Int> {
    if self == Self::ZERO {
      TryDecoded::Zero
    } else if self == Self::NAR {
      TryDecoded::NaR
    } else {
      // SAFETY: `self` is not 0 or NaR
      TryDecoded::Regular(unsafe { self.decode_regular() })
    }
  }

  /// Decode a posit **which is not 0 or NaR** into its constituent `frac`tion and `exp`onent.
  ///
  /// `self` cannot be 0 or NaR, or calling this is undefined behaviour.
  pub(crate) unsafe fn decode_regular(self) -> Decoded<N, ES, Int> {
    // This routine is central to nearly every nontrivial algorithm, so it's critical to get right!
    // With care, we can make it as small as ~20 instructions and ~7 cycles throughput on a modern
    // x86 CPU.
    //
    // Posits are interpreted in two's complement; the naïve way to decode them would be to take
    // the absolute value, extract the regime, exponent, and fraction fields, then negate the
    // fraction based on the sign of the original number.
    //
    // However, this entails branches (or at least `cmov`s). We can be clever and avoid this, and
    // work with the original number entirely, avoiding branches and the unecessary work of
    // negating the final result!
    //
    // We also use trickery to avoid branches in the regime decoding, which is different depending
    // on whether the regime bits are a run of 000s ended by a 1, or a run of 111s ended by a 0.

    // Shift out the JUNK_BITS, if they exist
    let x = self.0 << Self::JUNK_BITS;
    debug_assert!(
      x != Int::ZERO && x != Int::MIN,
      "Safety precondition violated: {self:?} cannot be 0 or NaR",
    );

    // Shift out the sign bit and count length of the initial run of 0s or 1s. `regime_raw` will be
    // that value minus 1.
    //
    // Example:
    //   x          = 0b10001..
    //   x << 1     = 0b0001...
    //   x_xor      = 0b1001...
    //   x_xor << 1 = 0b001....
    //   regime_raw = 2
    //
    // Example:
    //   x          = 0b011110..
    //   x << 1     = 0b11110...
    //   x_xor      = 0b10001...
    //   x_xor << 1 = 0b0001....
    //   regime_raw = 3
    let x_xor = x ^ (x << 1);
    let regime_raw = unsafe { (x_xor << 1).leading_zeros_nonzero() };
    debug_assert!(regime_raw <= Self::BITS - 2);

    // Now, the regime bits are supposed to encode a regime
    //
    //   n-1, if the regime bits are a run of n 1s terminated by a 0
    //   -n,  if the regime bits are a run of n 0s terminated by a 1
    //
    // But also, if the number is negative, we are supposed to take the two's complement before
    // interpreting these bits, which flips these bits (and adds one, but in all cases this one
    // will be "absorbed" by the other fields to the right of it, more on that later). But we have
    // a number that is precisely
    //
    //   0, if the regime is a run of 0s and the sign bit is 0 (positive)
    //      or the regime is a run of 1s and the sign bit is 1 (negative)
    //   1, if the regime is a run of 1s and the sign bit is 0 (positive)
    //      or the regime is a run of 0s and the sign bit is 1 (negative)
    //
    // It is the msb of `x_xor`, which is the sign bit xor the regime bit! But remember that in
    // two's complement `-n = -n + 1 - 1 = -(n - 1) - 1 = !(n - 1) + 1 - 1 = !(n - 1)`. So we can
    // work with `regime_raw` directly and have regime be
    //
    //   n-1 = regime_raw,  if the msb of x_xor is 1
    //   -n  = !regime_raw, if the msb of x_xor is 0
    //
    // If this is somewhat tricky to see that it's correct, use pen and paper to work it out
    // (or trust the tests)!
    let regime = Int::of_u32(regime_raw).not_if_positive(x_xor);

    // Shift out sign and regime bits (1 sign bit, regime_raw + 1 run of 0s or 1s, 1 terminating 0
    // or 1).
    let y = (x << regime_raw) << 3;

    // The rightmost `ES` bits of `y` are the exponent. However, we still need to negate them if
    // the Posit is negative (remember, we are supposed to interpret the fields from the two's
    // complement absolute value of its bits).
    //
    // A detail is that this is where the carry comes in TODO ELABORATE
    let exponent = y.not_if_negative(x).lshr(Int::BITS - Self::ES);  // Logical, not arithmetic shift

    // The rest of the bits of `y` are the fraction. Here we *don't* need to do anything about the
    // two's complement absolute value, since the `frac` we want to decode is signed (with the
    // same sign as the posit, of course). We just need to shift out the leftmost ES bits from
    // `y`.
    let fraction =
      // Compile-time special case if ES == 2 case, since it's a common choice (the standard's
      // choice!) and we can do it with 1 less instruction.
      if const { Self::ES == 2 } {
        // TODO Benchmark whether this is actually faster! It's a movabs+and instead of a shl+shr
        y.mask_lsb(Int::BITS - 2)
      } else {
        y.shl(Self::ES).lshr(2)
      };

    // Finally, assemble the frac (= fraction bits + hidden bits) and exp (= regime × 2^ES +
    // exponent).
    //
    // A note about the hidden bits: the fraction bits always have an implicit `1.0` factor
    // (meaning the `fffff` fraction bits encode a value `1.fffff`). For negative numbers this a
    // factor of `-1`. TODO ELABORATE
    let frac = Int::MIN.lshr(x.is_positive() as u32) + fraction;
    let exp = (regime << Self::ES) + exponent;
    Decoded{frac, exp}
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Decoded<N, ES, Int> {
  /// Aux function, for debug prints
  fn bin(x: Int) -> Posit<N, ES, Int> { Posit(x >> Posit::<N, ES, Int>::JUNK_BITS) }

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
  /// don't need to round, see [`Self::encode`].
  pub(crate) unsafe fn encode_regular_round(self, mut sticky: Int) -> Posit<N, ES, Int> {
    debug_assert!(
      self.is_normalised(),
      "Safety precondition violated: {:?} cannot have an underflowing frac", self.frac,
    );

    // Posit rounding rules state that, for positive number, any number > MAX is rounded to MAX,
    // and any number < MIN_POSITIVE is rounded to MIN_POSITIVE, and conversely for negative
    // numbers, any number < MIN is rounded to MIN, and any number > MAX_NEGATIVE is rounded to MAX_NEGATIVE.
    //
    // Equivalently, this just means that we have to clamp the exponent to the representable range;
    // since representing a number with max or min exp results in all fraction bits being shifted
    // out, we can ignore correcting the fraction.
    //
    // However, remember negative numbers have their exponent range shifted down 1 unit, since e.g.
    // the number MAX is represented as 1.0 × 2^MAX_EXP, but the number MIN is represented as 
    // -2.0 × 2^(MAX_EXP-1); see the documentation for [`Decoded::frac`] for more on this.
    /*dbg!(self);*/
    let frac = self.frac;
    let exp =
      // TODO improve (mark unpredictable? find bitwise trick?)
      if frac.is_positive() {
        self.exp.clamp(Posit::<N, ES, Int>::MIN_EXP, Posit::<N, ES, Int>::MAX_EXP)
      } else {
        self.exp.clamp(Posit::<N, ES, Int>::MIN_EXP - Int::ONE, Posit::<N, ES, Int>::MAX_EXP - Int::ONE)
      };
    /*dbg!(Self{frac, exp});*/

    // Extract the regime part of the exponent (bits higher than the lowest ES)
    let regime = exp >> ES;

    // The msb of the result, i.e. the sign bit, is the msb of `frac`.
    let sign_bits = frac.mask_msb(1);

    // Now for the regime bits, we want to create the following bits (let n be the value of
    // `regime` and s be the `sign` of the overall posit):
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
    let frac_xor_regime = frac ^ exp;
    let regime_raw = regime.not_if_negative(regime).as_u32();
    let regime_bits = (!frac_xor_regime).mask_msb(2) >> regime_raw;
    /*dbg!(regime_raw);*/

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
    let exponent_bits = exp.not_if_negative(frac) << (Int::BITS - ES);
    let fraction_bits = (frac << 2).lshr(Self::ES);
    let exponent_and_fraction_bits = exponent_bits | fraction_bits;
    /*dbg!(Self::bin(exponent_and_fraction_bits));*/
    let exponent_and_fraction_bits = exponent_and_fraction_bits.lshr(Posit::<N, ES, Int>::JUNK_BITS);

    // Now comes the tricky part: the rounding. The rounding rules translate to a very simple rule
    // in terms of bit patterns: just "represent as an infinite-precision bit string, then
    // round to nearest, if tied round to even bit pattern".
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

    // If Self::ES > 2, then we lost some bits of fraction already
    if const { Self::ES > 2 } {
      sticky |= frac.mask_lsb(Self::ES - 2)
    };
    // If there are JUNK_BITS, likewise
    if const { Posit::<N, ES, Int>::JUNK_BITS > 0 } {
      sticky |= frac.mask_lsb(Posit::<N, ES, Int>::JUNK_BITS);
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
    let even = exponent_and_fraction_bits.get_lsb();
    // Finally, we have the result of whether we need to round or not
    let round_up: bool = round & (even | (sticky != Int::ZERO));
    /*dbg!(round, even, sticky, round_up);*/


    // Assemble the final result, and return
    /*dbg!(
      Self::bin(sign_bits),
      Self::bin(regime_bits.lshr(1)),
      Self::bin(exponent_bits.lshr(3).lshr(regime_raw)),
      Self::bin(fraction_bits.lshr(3).lshr(regime_raw)),
      round,
    );*/
    let bits =
      ((sign_bits + regime_bits.lshr(1)) >> Posit::<N, ES, Int>::JUNK_BITS)
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
      "Safety precondition violated: {:?} cannot have an underflowing frac", self.frac,
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

  /// Hand-written examples for a 6-bit positive with 2-bit exponent (cf. Posit Arithmetic, John L.
  /// Gustafson, Chapter 2).
  // const POSIT_6_2: &[(Posit<6, 2, i32>, Decoded<6, 2, i32>)] = &[
  fn posit_6_2() -> impl Iterator<Item = (Posit<6, 2, i32>, Decoded<6, 2, i32>)> {
    [
      // Pos
      (0b000001, 0b01_000_0, -16),
      (0b000010, 0b01_000_0, -12),
      (0b000011, 0b01_000_0, -10),
      (0b000100, 0b01_000_0, -8),
      (0b000101, 0b01_000_0, -7),
      (0b000110, 0b01_000_0, -6),
      (0b000111, 0b01_000_0, -5),
      (0b001000, 0b01_000_0, -4),
      (0b001001, 0b01_100_0, -4),
      (0b001010, 0b01_000_0, -3),
      (0b001011, 0b01_100_0, -3),
      (0b001100, 0b01_000_0, -2),
      (0b001101, 0b01_100_0, -2),
      (0b001110, 0b01_000_0, -1),
      (0b001111, 0b01_100_0, -1),
      (0b010000, 0b01_000_0, 0),  // One
      (0b010001, 0b01_100_0, 0),
      (0b010010, 0b01_000_0, 1),
      (0b010011, 0b01_100_0, 1),
      (0b010100, 0b01_000_0, 2),
      (0b010101, 0b01_100_0, 2),
      (0b010110, 0b01_000_0, 3),
      (0b010111, 0b01_100_0, 3),
      (0b011000, 0b01_000_0, 4),
      (0b011001, 0b01_000_0, 5),
      (0b011010, 0b01_000_0, 6),
      (0b011011, 0b01_000_0, 7),
      (0b011100, 0b01_000_0, 8),
      (0b011101, 0b01_000_0, 10),
      (0b011110, 0b01_000_0, 12),
      (0b011111, 0b01_000_0, 16),
      // Neg
      (-0b000001, 0b10_000_0, -16 - 1),
      (-0b000010, 0b10_000_0, -12 - 1),
      (-0b000011, 0b10_000_0, -10 - 1),
      (-0b000100, 0b10_000_0, -8 - 1),
      (-0b000101, 0b10_000_0, -7 - 1),
      (-0b000110, 0b10_000_0, -6 - 1),
      (-0b000111, 0b10_000_0, -5 - 1),
      (-0b001000, 0b10_000_0, -4 - 1),
      (-0b001001, 0b10_100_0, -4),
      (-0b001010, 0b10_000_0, -3 - 1),
      (-0b001011, 0b10_100_0, -3),
      (-0b001100, 0b10_000_0, -2 - 1),
      (-0b001101, 0b10_100_0, -2),
      (-0b001110, 0b10_000_0, -1 - 1),
      (-0b001111, 0b10_100_0, -1),
      (-0b010000, 0b10_000_0, 0 - 1),  // Minus one
      (-0b010001, 0b10_100_0, 0),
      (-0b010010, 0b10_000_0, 1 - 1),
      (-0b010011, 0b10_100_0, 1),
      (-0b010100, 0b10_000_0, 2 - 1),
      (-0b010101, 0b10_100_0, 2),
      (-0b010110, 0b10_000_0, 3 - 1),
      (-0b010111, 0b10_100_0, 3),
      (-0b011000, 0b10_000_0, 4 - 1),
      (-0b011001, 0b10_000_0, 5 - 1),
      (-0b011010, 0b10_000_0, 6 - 1),
      (-0b011011, 0b10_000_0, 7 - 1),
      (-0b011100, 0b10_000_0, 8 - 1),
      (-0b011101, 0b10_000_0, 10 - 1),
      (-0b011110, 0b10_000_0, 12 - 1),
      (-0b011111, 0b10_000_0, 16 - 1),
    ].iter().map(|&(bits, frac, exp)| {
      let frac = frac << (32 - 6);
      (Posit::from_bits(bits), Decoded { frac, exp })
    })
  }

  #[test]
  fn posit_6_2_correctness() {
    // Assert that `posit_6_2()` contains all posits
    assert_eq!(
      posit_6_2().map(|(posit, _)| posit).collect::<Vec<_>>().as_slice(),
      Posit::<6, 2, i32>::cases_exhaustive().collect::<Vec<_>>().as_slice(),
    );
    // And that the decoded values are correct
    for (posit, decoded) in posit_6_2() {
      assert_eq!(Rational::try_from(posit), Ok(Rational::from(decoded)))
    }
  }

  mod decode {
    use super::*;

    #[test]
    fn posit_6_2_manual() {
      for (posit, decoded) in posit_6_2() {
        assert_eq!(unsafe { posit.decode_regular() }, decoded)
      }
    }

    fn decode<const N: u32, const ES: u32, Int: crate::Int>(p: Posit<N, ES, Int>) -> Decoded<N, ES, Int> {
      let TryDecoded::Regular(decoded) = p.try_decode() else { panic!("Invalid test case") };
      decoded
    }

    // Rule of thumb: in release builds, including the conversions to rational, 1-3us per iteration,
    // or 300k-1000k checks per second.

    #[test]
    fn p8_exhaustive() {
      for p in Posit::<8, 2, i8>::cases_exhaustive() {
        assert_eq!(Rational::try_from(p), Ok(Rational::from(decode(p))))
      }
    }

    #[test]
    fn p16_exhaustive() {
      for p in Posit::<16, 2, i16>::cases_exhaustive() {
        assert_eq!(Rational::try_from(p), Ok(Rational::from(decode(p))))
      }
    }

    const PROPTEST_CASES: u32 = if cfg!(debug_assertions) {0x1_0000} else {0x80_0000};
    proptest!{
      #![proptest_config(ProptestConfig::with_cases(PROPTEST_CASES))]

      #[test]
      fn p32_proptest(p in Posit::<32, 2, i32>::cases_proptest()) {
        assert_eq!(Rational::try_from(p), Ok(Rational::from(decode(p))))
      }

      #[test]
      fn p64_proptest(p in Posit::<64, 2, i64>::cases_proptest()) {
        assert_eq!(Rational::try_from(p), Ok(Rational::from(decode(p))))
      }
    }

    #[test]
    fn posit_10_1_exhaustive() {
      for p in Posit::<10, 1, i32>::cases_exhaustive() {
        assert_eq!(Rational::try_from(p), Ok(Rational::from(decode(p))))
      }
    }

    #[test]
    fn posit_20_4_exhaustive() {
      for p in Posit::<20, 4, i32>::cases_exhaustive() {
        assert_eq!(Rational::try_from(p), Ok(Rational::from(decode(p))))
      }
    }
  }

  mod roundtrip {
    use super::*;

    #[test]
    fn posit_6_2_manual() {
      for (posit, _) in posit_6_2() {
        assert_eq!(unsafe { posit.decode_regular().encode_regular() }, posit)
      }
    }

    fn assert_roundtrip<const N: u32, const ES: u32, Int: crate::Int>(p: Posit<N, ES, Int>) {
      let TryDecoded::Regular(decoded) = p.try_decode() else { panic!("Invalid test case") };
      assert_eq!(decoded.try_encode(), Some(p))
    }

    #[test]
    fn p8_exhaustive() {
      for p in Posit::<8, 2, i8>::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }

    #[test]
    fn p16_exhaustive() {
      for p in Posit::<16, 2, i16>::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }

    const PROPTEST_CASES: u32 = if cfg!(debug_assertions) {0x1_0000} else {0x80_0000};
    proptest!{
      #![proptest_config(ProptestConfig::with_cases(PROPTEST_CASES))]

      #[test]
      fn p32_proptest(p in Posit::<32, 2, i32>::cases_proptest()) {
        assert_roundtrip(p)
      }

      #[test]
      fn p64_proptest(p in Posit::<64, 2, i64>::cases_proptest()) {
        assert_roundtrip(p)
      }
    }

    #[test]
    fn posit_10_1_exhaustive() {
      for p in Posit::<10, 1, i32>::cases_exhaustive() {
        assert_roundtrip(p)
      }
    }

    #[test]
    fn posit_20_4_exhaustive() {
      for p in Posit::<20, 4, i32>::cases_exhaustive() {
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
