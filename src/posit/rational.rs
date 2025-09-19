use super::*;

use crate::Quire;

use malachite::{Integer, rational::Rational};
use malachite::base::num::arithmetic::traits::{PowerOf2, Pow, Abs, Reciprocal};

/// A shortcut trait with a couple helper functions.
pub trait IntExt: crate::Int {
  fn pow(self, other: Self) -> Rational {
    let exp: i128 = other.into();
    let exp: i64 = exp.try_into().expect("Exponent overflow in converting to rational");
    Rational::pow(Rational::from(self.into()), exp)
  }

  fn power_of_2(self) -> Rational {
    let exp: i128 = self.into();
    let exp: i64 = exp.try_into().expect("Exponent overflow in converting to rational");
    Rational::power_of_2(exp)
  }
}

impl IntExt for i128 {}
impl IntExt for i64 {}
impl IntExt for i32 {}
impl IntExt for i16 {}
impl IntExt for i8 {}

/// The error type returned when a [Posit] cannot be converted to a [Rational] because it is
/// [NaR](Posit::NAR).
#[derive(Debug)]
#[derive(PartialEq, Eq)]
pub struct IsNaR;

impl<
  const N: u32,
  const ES: u32,
  Int: IntExt,
> Posit<N, ES, Int>
where
  Integer: From<Int>,
  Rational: From<Int>,
  Rational: From<Int::Unsigned>,
{
  /// Convert a posit **which is not 0 or NaR** into a [Rational] value. Panics if `self` is 0 or
  /// NaR.
  ///
  /// This is a **super-explicit** and **super-obvious** rendition of the algorithm for decoding a
  /// posit, since this is what we will check our optimised implementations against!
  fn into_rational_regular(self) -> Rational {
    // Shift out the junk bits, which are the leftmost bits in case N < Int::BITS.
    let x = self.0 << Self::JUNK_BITS;

    // If the number if NaR or 0, panic.
    if x == Int::ZERO || x == Int::MIN { panic!("Should not pass {x:b} to into_rational_regular") }

    // First extract the sign; the rest of the algorithm takes place with the two's complement
    // absolute value of the posit.
    let sign = !x.is_positive();
    let x = x.abs();

    // Shift out the sign bit (N-1), the next one (N-2) is the sign of the regime. If it's 0, we
    // are looking for the number of consecutive 0s terminated by 1, if it's 1, we are looking for
    // the number of consecutive 1s terminated by 0. In the case of a run of 1s, it may also go
    // all the way to the end of the number.
    let x = x << 1;
    let regime_sign = !x.is_positive() as u8;
    let regime_len =
      if regime_sign == 0 {
        // Run of 0s followed by 1; note that the terminating 1 is always present, because `x` is
        // not NaR (0b1000…) or 0 (0b0000…).
        x.leading_zeros()
      } else {
        // Run of 1s folloed by 0 or by the end of the posit; note that if the latter case, we have
        // shifted x 1 place to the right so we have shifted a terminating 0 in anyways.
        (!x).leading_zeros()
      };
    // The regime is
    //   -n  if it's a run of n 0s, or
    //   n-1 if it's a run of n 1s.
    let regime = if regime_sign == 0 { -(regime_len as i32) } else { regime_len as i32 - 1 };

    // Shift out the regime bits incl. the terminating bit. After this, the leftmost ES bits are
    // the exponent, so we just shift those down to the rightmost ES bits and we have our
    // exponent.
    //
    // Note that if there are less than ES bits leftover after the regime, the exponent may be
    // partially or even totally missing; this is okay, since in this case we have to fill in 0s
    // from the right, which is exactly what the shift does.
    let x = (x << regime_len) << 1;
    let exponent = if const { Self::ES != 0 } {x.lshr(Int::BITS - Self::ES)} else {Int::ZERO};

    // Shift out the exponent bits. After this we have the fraction bits starting from the left.
    //
    // The fraction bits start from the left, so they will represent the numerator of
    // an **unsigned** fraction with denominator 2 ^ Int::BITS. Remember, it is unsigned because
    // we are working with the two's complement absolute value (the sign has been extracted
    // first).
    //
    // There is always an implicit/hidden bit of 1 so the fraction bits ffff will represent 1.ffff,
    // i.e. 1 + ffff / 2 ^ int::BITS.
    //
    // Again the fraction bits may be partially or even totally missing, and again we fill in 0s
    // from the right when we shift.
    let fraction = (x << Self::ES).as_unsigned();

    // Assemble the final number
    let useed = IntExt::power_of_2(Int::ONE << Self::ES);

    let sign = (-Int::ONE).pow(Int::from(sign));
    let regime = useed.pow(regime as i64);
    let exponent = IntExt::power_of_2(exponent);
    let fraction = Rational::from(Int::ONE) + (Rational::from(fraction) / Rational::power_of_2(Int::BITS as i64));

    sign * regime * exponent * fraction
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: IntExt,
> TryFrom<Posit<N, ES, Int>> for Rational
where
  Integer: From<Int>,
  Rational: From<Int>,
  Rational: From<Int::Unsigned>,
{
  type Error = IsNaR;

  fn try_from(value: Posit<N, ES, Int>) -> Result<Self, Self::Error> {
    if value == Posit::ZERO {
      Ok(Rational::from(Int::ZERO))
    } else if value == Posit::NAR {
      Err(IsNaR)
    } else {
      Ok(value.into_rational_regular())
    }
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: IntExt,
> From<Decoded<N, ES, Int>> for Rational
where
  Integer: From<Int>,
  Int: malachite::base::num::basic::signeds::PrimitiveSigned,
{
  fn from(value: Decoded<N, ES, Int>) -> Self {
    let frac = Rational::from_signeds(value.frac, Decoded::<N, ES, Int>::FRAC_DENOM);
    let exp = IntExt::power_of_2(value.exp);
    frac * exp
  }
}

impl<
  const N: u32,
  const ES: u32,
  const BYTES: usize,
> TryFrom<Quire<N, ES, BYTES>> for Rational {
  type Error = IsNaR;

  fn try_from(value: Quire<N, ES, BYTES>) -> Result<Self, Self::Error> {
    if value.is_nar() {
      Err(IsNaR)
    } else {
      // The quire is just big fix-point number with denominator 2 ^ WIDTH.
      let mut bytes = value.0.iter();

      let first = bytes.next().unwrap();  // First (most significant) byte is signed i8
      let mut numerator = Integer::from(*first as i8);

      for rest in bytes {  // The other bytes are unsigned u8
        numerator *= Integer::from(1 << 8);
        numerator += Integer::from(*rest as i16);
      };

      let denominator = Integer::power_of_2(Quire::<N, ES, BYTES>::WIDTH as u64);
      Ok(Rational::from_integers(numerator, denominator))
    }
  }
}

/// Check whether the rational number `exact` should be rounded to `posit`.
///
///   - Over- or under-flow (exponent < [Posit::MIN_EXP] or > [Posit::MIN_EXP]: round to
///     [Posit::MIN] or [Posit::MAX] respectively.
///   - Geometric case (exponent < [Posit::MIN_NORMAL_EXP] or >[Posit::MIN_NORMAL_EXP]: round to
///     nearest posit in terms of absolute **ratio**, ties to even.
///   - Normal case (remaining domain): round to nearest posit in terms of absolute **difference**,
///     ties to even.
pub fn is_correct_rounded<const N: u32, const ES: u32, Int: crate::Int>(
  exact: Rational,
  posit: Posit<N, ES, Int>,
) -> bool
where
  Rational: TryFrom<Posit<N, ES, Int>, Error = IsNaR>,
{
  // Only the exact number 0 is rounded to posit 0.
  if posit == Posit::<N, ES, Int>::ZERO { return exact == Rational::from(0) }
  // No number is rounded to posit NaR.
  if posit == Posit::<N, ES, Int>::NAR { return false }

  // Overflow case: if exact is > MAX, < MIN, > 0 and < MIN_POSITIVE, or < 0 and > MAX_NEGATIVE
  if exact > Rational::from(0) {
    if exact >= Rational::try_from(Posit::<N, ES, Int>::MAX).unwrap() {
      return posit == Posit::<N, ES, Int>::MAX
    }
    else if exact <= Rational::try_from(Posit::<N, ES, Int>::MIN_POSITIVE).unwrap() {
      return posit == Posit::<N, ES, Int>::MIN_POSITIVE
    }
  } else if exact < Rational::from(0) {
    if exact <= Rational::try_from(Posit::<N, ES, Int>::MIN).unwrap() {
      return posit == Posit::<N, ES, Int>::MIN
    }
    else if exact >= Rational::try_from(Posit::<N, ES, Int>::MAX_NEGATIVE).unwrap() {
      return posit == Posit::<N, ES, Int>::MAX_NEGATIVE
    }
  } else {
    unreachable!()
  }

  // Remaining cases: round to nearest (arithmetic nearest, or geometric nearest *only if* exponent
  // bits are cut). `distance` uses arithmetic or geometric distance accordingly.
  let distance = {
    // If `1 + regime_len + 1 + Self::ES > Self::BITS`, i.e. on the edges of the posit's dynamic
    // range, some exponent bits are chopped and hence we are in a region of geometric rounding.
    //
    // So if `regime_len ≤ Self::BITS - 2 - Self::ES`, we are in the arithmetic rounding region,
    // otherwise we're on the geometric rounding region. This `regime_len` corresponds to an
    // exponent of `(Self::BITS - 2 - Self::ES) << Self::ES`..
    let geometric_cutoff = Rational::power_of_2(((N - 2 - ES) as i64) << ES);
    let arithmetic_range = (&geometric_cutoff).reciprocal() ..= geometric_cutoff;
    let is_arithmetic_rounding = arithmetic_range.contains(&(&exact).abs());

    move |x: &Rational, y: &Rational| {
      if is_arithmetic_rounding {
        x-y
      } else {
        if x.abs() >= y.abs() {x/y} else {y/x}
      }
    }
  };

  // `posit` represents exactly the number `curr`, while the immediately previous and next posits
  // represent exactly the numbers `prev` and `next`, respectively.
  let prev = Rational::try_from(posit.prior());
  let curr = Rational::try_from(posit).unwrap();
  let next = Rational::try_from(posit.next());
  let posit_is_even = posit.to_bits() & Int::ONE == Int::ZERO;

  if exact == curr {
    // `exact` is exactly represented by `posit`
    true
  } else if let Ok(prev) = prev && prev < exact && exact < curr {
    // `exact` lies in interval `]posit.prior(), posit[`: needs to be closer to `posit` than to
    // `posit.prior()`, or same distance if `posit` is even.
    let distance_curr = distance(&curr, &exact);
    let distance_prev = distance(&exact, &prev);
    distance_curr < distance_prev || distance_curr == distance_prev && posit_is_even
  } else if let Ok(next) = next && curr < exact && exact < next {
    // `exact` lies in interval `]posit, posit.next()[`: needs to be closer to `posit` than to
    // `posit.next()`, or same distance if `posit` is even.
    let distance_curr = distance(&exact, &curr);
    let distance_next = distance(&next, &exact);
    distance_curr < distance_next || distance_curr == distance_next && posit_is_even
  } else {
    // Not in interval
    false
  }
}

pub fn try_is_correct_rounded<const N: u32, const ES: u32, Int: crate::Int>(
  exact: Result<Rational, IsNaR>,
  posit: Posit<N, ES, Int>,
) -> bool
where
  Rational: TryFrom<Posit<N, ES, Int>, Error = IsNaR>,
{
  match exact {
    Ok(exact) => is_correct_rounded(exact, posit),
    Err(IsNaR) => posit == Posit::NAR,
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  /// Manually test all bit patterns for a 6-bit positive with 2-bit exponent (cf. Posit
  /// Arithmetic, John L. Gustafson, Chapter 2).
  #[test]
  fn exhaustive_posit_6_2() {
    type Posit = super::Posit<6, 2, i16>;

    assert_eq!(Rational::try_from(Posit::from_bits(0b000000)), Ok(Rational::from(0)));
    assert_eq!(Rational::try_from(Posit::from_bits(0b100000)), Err(IsNaR));

    for (bits, (num, den)) in [
      (0b000001, (1, 65536)),
      (0b000010, (1, 4096)),
      (0b000011, (1, 1024)),
      (0b000100, (1, 256)),
      (0b000101, (1, 128)),
      (0b000110, (1, 64)),
      (0b000111, (1, 32)),
      (0b001000, (2, 32)),
      (0b001001, (3, 32)),
      (0b001010, (4, 32)),
      (0b001011, (6, 32)),
      (0b001100, (8, 32)),
      (0b001101, (12, 32)),
      (0b001110, (16, 32)),
      (0b001111, (24, 32)),
      (0b010000, (1, 1)),
      (0b010001, (3, 2)),
      (0b010010, (2, 1)),
      (0b010011, (3, 1)),
      (0b010100, (4, 1)),
      (0b010101, (6, 1)),
      (0b010110, (8, 1)),
      (0b010111, (12, 1)),
      (0b011000, (16, 1)),
      (0b011001, (32, 1)),
      (0b011010, (64, 1)),
      (0b011011, (128, 1)),
      (0b011100, (256, 1)),
      (0b011101, (1024, 1)),
      (0b011110, (4096, 1)),
      (0b011111, (65536, 1)),
    ] {
      assert_eq!(Posit::from_bits( bits).try_into(), Ok(Rational::from_signeds( num, den)));
      assert_eq!(Posit::from_bits(-bits).try_into(), Ok(Rational::from_signeds(-num, den)));
    }
  }

  /// More manual examples from the notebook.
  #[test]
  #[allow(overflowing_literals)]
  fn examples() {
    assert_eq!(Posit::<6, 1, i8>::from_bits(0b100001).try_into(), Ok(Rational::from(-256)));
    assert_eq!(Posit::<6, 1, i8>::from_bits(0b000001).try_into(), Ok(Rational::from_signeds(1, 256)));
    assert_eq!(Posit::<6, 1, i8>::from_bits(0b001101).try_into(), Ok(Rational::from_signeds(5, 8)));
    assert_eq!(Posit::<6, 1, i8>::from_bits(0b110010).try_into(), Ok(Rational::from_signeds(-3, 4)));

    assert_eq!(Posit::<16, 2, i16>::from_bits(0b0_01_00_10000001000).try_into(), Ok(Rational::from_signeds(3080, 1 << 15)));
    assert_eq!(Posit::<16, 2, i16>::from_bits(0b0_01_00_11011001000).try_into(), Ok(Rational::from_signeds(3784, 1 << 15)));
    assert_eq!(Posit::<16, 2, i16>::from_bits(0b0_01_00_11011001000).try_into(), Ok(Rational::from_signeds(3784, 1 << 15)));
    assert_eq!(Posit::<16, 2, i16>::from_bits(0b0_01_01_11011001000).try_into(), Ok(Rational::from_signeds(3784, 1 << 14)));
    assert_eq!(Posit::<16, 2, i16>::from_bits(0b0_01_10_11011001000).try_into(), Ok(Rational::from_signeds(3784, 1 << 13)));
    assert_eq!(Posit::<16, 2, i16>::from_bits(0b0_01_11_11011001000).try_into(), Ok(Rational::from_signeds(3784, 1 << 12)));
    assert_eq!(Posit::<16, 2, i16>::from_bits(0b0_11110_10_11001000).try_into(), Ok(Rational::from(456 << 6)));
    assert_eq!(Posit::<16, 2, i16>::from_bits(0b0_11110_01_11001000).try_into(), Ok(Rational::from(456 << 5)));

    assert_eq!(Posit::<16, 2, i16>::from_bits(0b1_00001_10_00111000).try_into(), Ok(Rational::from(-456 << 5)));
    assert_eq!(Posit::<16, 2, i16>::from_bits(0b1_00001_01_00111000).try_into(), Ok(Rational::from(-456 << 6)));
    assert_eq!(Posit::<16, 2, i16>::from_bits(0b1_001_01_0100111000).try_into(), Ok(Rational::from_signeds(-1736, 1 << 4)));
    assert_eq!(Posit::<16, 2, i16>::from_bits(0b1_1110_10_100111000).try_into(), Ok(Rational::from_signeds(-712, 1 << 20)));

    assert_eq!(Posit::<16, 2, i16>::from_bits(0b1_11111111111110_1_).try_into(), Ok(Rational::from_signeds(-1, 1i64 << 50)));
    assert_eq!(Posit::<16, 2, i16>::from_bits(0b1_11111111111110_0_).try_into(), Ok(Rational::from_signeds(-1, 1i64 << 48)));
    assert_eq!(Posit::<16, 2, i16>::from_bits(0b0_11111111110_00_10).try_into(), Ok(Rational::from(3i64 << 35)));

    assert_eq!(Posit::<16, 2, i16>::MAX.try_into(), Ok(Rational::from(1i64 << 56)));
    assert_eq!(Posit::<16, 2, i16>::MIN.try_into(), Ok(Rational::from(-1i64 << 56)));
    assert_eq!(Posit::<16, 2, i16>::MIN_POSITIVE.try_into(), Ok(Rational::from_signeds(1, 1i64 << 56)));
    assert_eq!(Posit::<16, 2, i16>::MAX_NEGATIVE.try_into(), Ok(Rational::from_signeds(1, -1i64 << 56)));

    assert_eq!(Posit::<16, 2, i16>::ZERO.try_into(), Ok(Rational::from(0)));
    assert_eq!(Posit::<16, 2, i16>::ONE.try_into(), Ok(Rational::from(1)));
    assert_eq!(Posit::<16, 2, i16>::MINUS_ONE.try_into(), Ok(Rational::from(-1)));
    assert_eq!(Rational::try_from(Posit::<16, 2, i16>::NAR), Err(IsNaR));
  }

  #[test]
  fn quire() {
    let bits = [
      0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    assert_eq!(Rational::try_from(crate::q8::from_bits(bits)), Ok(Rational::from(1)));
    let bits = [
      0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 123,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    assert_eq!(Rational::try_from(crate::q8::from_bits(bits)), Ok(Rational::from(123)));
    let bits = [
      0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 234, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    assert_eq!(Rational::try_from(crate::q8::from_bits(bits)), Ok(Rational::from(234 << 8)));
    let bits = [
      0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 123, 0x00, 0x00, 0x00, 0x00,
    ];
    assert_eq!(Rational::try_from(crate::q8::from_bits(bits)), Ok(Rational::from_signeds(123, 1 << 16)));
    let bits = [
      0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    assert_eq!(Rational::try_from(crate::q8::from_bits(bits)), Ok(Rational::from(-1)));
    let bits = [
      0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xf0, 0x00, 0x00, 0x00, 0x00,
    ];
    assert_eq!(Rational::try_from(crate::q8::from_bits(bits)), Ok(Rational::from_signeds(-1, 1 << 12)));
    let bits = [
      0x00, 0x00, 0x00, 0x10,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    assert_eq!(Rational::try_from(crate::q8::from_bits(bits)), Ok(Rational::power_of_2(8 * 6 + 4_i64)));

    assert_eq!(Rational::try_from(crate::q32::NAR), Err(IsNaR))
  }
}
