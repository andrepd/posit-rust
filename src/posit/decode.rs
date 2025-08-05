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
    let exponent = if const { Self::ES != 0 } {y.not_if_negative(x).lshr(Int::BITS - Self::ES)} else {Int::ZERO};  // Logical, not arithmetic shift

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

#[cfg(test)]
mod tests {
  use super::*;

  use malachite::rational::Rational;
  use proptest::prelude::*;
  use super::test::posit_6_2;

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
