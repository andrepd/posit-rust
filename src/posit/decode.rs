use super::*;

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
    debug_assert!(x != Int::ZERO && x != Int::MIN, "Safety precondition violated: {:?} cannot be 0 or NaR", self);

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
    debug_assert!(regime_raw as u32 <= Self::BITS - 2);

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

  #[test]
  fn posit_6_2_manual() {
    // Hand-written examples for a 6-bit positive with 2-bit exponent (cf. Posit Arithmetic, John
    // L. Gustafson, Chapter 2).
    for (x, frac, exp) in [
      // Pos
      (0b000001, 0b01_000_0, -16),
      (0b000010, 0b01_000_0, -12),
      (0b000011, 0b01_000_0, -10),
      (0b000100, 0b01_000_0, -8),
      (0b000101, 0b01_000_0, -7),
      (0b000110, 0b01_000_0, -6),
      (0b000111, 0b01_000_0, -5),

      (0b001100, 0b01_000_0, -2),
      (0b001101, 0b01_100_0, -2),
      (0b001110, 0b01_000_0, -1),
      (0b001111, 0b01_100_0, -1),
      (0b010000, 0b01_000_0, 0),  // One
      (0b010001, 0b01_100_0, 0),
      (0b010010, 0b01_000_0, 1),
      (0b010011, 0b01_100_0, 1),
      (0b010100, 0b01_000_0, 2),

      // Neg
      (-0b000001, 0b10_000_0, -16 - 1),
      (-0b000010, 0b10_000_0, -12 - 1),
      (-0b000011, 0b10_000_0, -10 - 1),
      (-0b000100, 0b10_000_0, -8 - 1),
      (-0b000101, 0b10_000_0, -7 - 1),
      (-0b000110, 0b10_000_0, -6 - 1),
      (-0b000111, 0b10_000_0, -5 - 1),

      (-0b001100, 0b10_000_0, -2 - 1),
      (-0b001101, 0b10_100_0, -2),
      (-0b001110, 0b10_000_0, -1 - 1),
      (-0b001111, 0b10_100_0, -1),
      (-0b010000, 0b10_000_0, 0 - 1),  // Minus one
      (-0b010001, 0b10_100_0, 0),
      (-0b010010, 0b10_000_0, 1 - 1),
      (-0b010011, 0b10_100_0, 1),
      (-0b010100, 0b10_000_0, 2 - 1),
    ] {
      let frac = frac << (64 - 6);
      assert_eq!(
        unsafe { Posit::<6, 2, i64>::from_bits(x).decode_regular() },
        Decoded { frac, exp },
      )
    }
  }

  use malachite::rational::Rational;
  use proptest::prelude::*;

  /// Check correctness of decode by enumerating all posits
  macro_rules! make_exhaustive {
    ($name:ident, $t:ty) => {
      #[test]
      fn $name() {
        for sign in [true, false] {
          for abs in (1 ..= (i128::MAX >> (128 - <$t>::BITS))) {
            let bits = if sign {abs} else {-abs};
            let posit = <$t>::from_bits(bits.try_into().unwrap());
            let TryDecoded::Regular(decoded) = posit.try_decode() else { panic!("Invalid test case") };
            assert_eq!(Rational::try_from(posit), Ok(Rational::from(decoded)))
          }
        }
      }
    }
  }

  /// Check correctness of decode by using proptest
  macro_rules! make_proptest {
    ($name:ident, $t:ty, $cases:literal) => {
      proptest! {
        #![proptest_config(ProptestConfig::with_cases($cases))]

        #[test]
        fn $name(
          sign in any::<bool>(),
          abs in (1 ..= (i128::MAX >> (128 - <$t>::BITS))),
        ) {
          let bits = if sign {abs} else {-abs};
          let posit = <$t>::from_bits(bits.try_into().unwrap());
          let TryDecoded::Regular(decoded) = posit.try_decode() else { panic!("Invalid test case") };
          assert_eq!(Rational::try_from(posit), Ok(Rational::from(decoded)))
        }
      }
    }
  }

  // Rule of thumb: in release builds, including the conversions to rational, 1-3us per iteration,
  // or 300k-1000k checks per second.

  make_exhaustive!{p8_exhaustive, Posit::<8, 2, i8>}

  make_exhaustive!{p16_exhaustive, Posit::<16, 2, i16>}

  #[cfg(debug_assertions)]
  make_proptest!{p32_exhaustive, Posit::<32, 2, i32>, 0x8_0000}

  #[cfg(not(debug_assertions))]
  make_proptest!{p32_exhaustive, Posit::<32, 2, i32>, 0x100_0000}

  #[cfg(debug_assertions)]
  make_proptest!{p64_exhaustive, Posit::<64, 2, i64>, 0x8_0000}

  #[cfg(not(debug_assertions))]
  make_proptest!{p64_exhaustive, Posit::<64, 2, i64>, 0x100_0000}

  make_exhaustive!{posit_6_2_exhaustive, Posit::<6, 2, i8>}

  make_exhaustive!{posit_10_1_exhaustive, Posit::<10, 1, i32>}

  make_exhaustive!{posit_20_4_exhaustive, Posit::<20, 4, i32>}
}
