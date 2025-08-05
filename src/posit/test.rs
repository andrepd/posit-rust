use super::*;
use crate::underlying::const_i128_as_int;
use core::ops::{RangeInclusive, Range};

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  /// Range of the absolute values of posit bit patterns, excluding 0 and NaR.
  const RANGE_ABS: RangeInclusive<i128> = 1 ..= (i128::MAX >> (128 - Self::BITS));

  /// An iterator through all the posits except 0 and NaR.
  pub(crate) fn cases_exhaustive() -> impl Iterator<Item = Self> {
    let pos = Self::RANGE_ABS.map(|abs| Self::from_bits(const_i128_as_int(abs)));
    let neg = Self::RANGE_ABS.map(|abs| Self::from_bits(const_i128_as_int(-abs)));
    pos.chain(neg)
  }

  /// An iterator through all the posits.
  pub(crate) fn cases_exhaustive_all() -> impl Iterator<Item = Self> {
    [Self::ZERO, Self::NAR].into_iter().chain(Self::cases_exhaustive())
  }

  /// A [proptest Strategy](proptest::strategy::Strategy) that yields any posit except 0 and NaR.
  pub(crate) fn cases_proptest() -> impl proptest::strategy::Strategy<Value = Self> {
    use proptest::prelude::*;
    (any::<bool>(), Self::RANGE_ABS).prop_map(|(sign, abs)| {
      let bits = if sign {abs} else {-abs};
      Self::from_bits(const_i128_as_int(bits))
    })
  }

  /// A [proptest Strategy](proptest::strategy::Strategy) that yields any posit.
  pub(crate) fn cases_proptest_all() -> impl proptest::strategy::Strategy<Value = Self> {
    use proptest::prelude::*;
    (Self::cases_proptest(), 0..Self::BITS).prop_map(|(posit, is_special)| {
      if is_special == 0 {
        if posit > Self::ZERO {Self::ZERO} else {Self::NAR}
      } else {
        posit
      }
    })
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Decoded<N, ES, Int> {
  /// Range of the absolute values of frac bit patterns, i.e. any number with leading `0b01`.
  const RANGE_FRAC_ABS: Range<i128> =
    (i128::MIN as u128 >> (128 - Int::BITS) >> 1) as i128
    .. (i128::MIN as u128 >> (128 - Int::BITS)) as i128;

  /// Range of the valid exponents, i.e. `3 * MIN_EXP ..= 3 * MAX_EXP`, which is the max value we
  /// guarantee is representable in a [Decoded].
  const RANGE_EXP: RangeInclusive<i128> =
    -3 * ((Self::BITS as i128 - 2) << Self::ES)
    ..= 3 * ((Self::BITS as i128 - 2) << Self::ES);

  /// An iterator through **all the valid values of [Self]**, including values that do not
  /// correspond exactly to a `posit.decode_regular()` call and hence need to be rounded.
  pub(crate) fn cases_exhaustive() -> impl Iterator<Item = Self> {
    Self::RANGE_EXP.flat_map(|exp| {
      let pos = Self::RANGE_FRAC_ABS.map(move |abs| Self {
        frac: const_i128_as_int(abs),
        exp: const_i128_as_int(exp),
      });
      let neg = Self::RANGE_FRAC_ABS.rev().map(move |abs| Self {
        frac: const_i128_as_int(!abs),
        exp: const_i128_as_int(exp),
      });
      pos.chain(neg)
    })
  }

  /// A [proptest Strategy](proptest::strategy::Strategy) that yields **all the valid values of
  /// [Self]**, including values that do not correspond exactly to a `posit.decode_regular()` call
  /// and hence need to be rounded.
  pub(crate) fn cases_proptest() -> impl proptest::strategy::Strategy<Value = Self> {
    use proptest::prelude::*;
    // Include exponents up to ±3× MAX_EXP, the max value we guarantee is representable in a
    // [Decoded].
    (any::<bool>(), Self::RANGE_FRAC_ABS, Self::RANGE_EXP).prop_map(|(sign, abs, exp)| {
      let frac = if sign {abs} else {!abs};
      Self { frac: const_i128_as_int(frac), exp: const_i128_as_int(exp)}
    })
  }
}

/// Hand-written examples for a 6-bit positive with 2-bit exponent (cf. Posit Arithmetic, John L.
/// Gustafson, Chapter 2).
// const POSIT_6_2: &[(Posit<6, 2, i32>, Decoded<6, 2, i32>)] = &[
pub fn posit_6_2() -> impl Iterator<Item = (Posit<6, 2, i32>, Decoded<6, 2, i32>)> {
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

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn cases_exhaustive() {
    assert_eq!(
      Posit::<4, 1, i8>::cases_exhaustive().collect::<Vec<_>>().as_slice(),
      [
        Posit::from_bits(0b0001),
        Posit::from_bits(0b0010),
        Posit::from_bits(0b0011),
        Posit::from_bits(0b0100),
        Posit::from_bits(0b0101),
        Posit::from_bits(0b0110),
        Posit::from_bits(0b0111),
        Posit::from_bits(0b1111),
        Posit::from_bits(0b1110),
        Posit::from_bits(0b1101),
        Posit::from_bits(0b1100),
        Posit::from_bits(0b1011),
        Posit::from_bits(0b1010),
        Posit::from_bits(0b1001),
      ]
    )
  }

  #[test]
  fn cases_exhaustive_all() {
    assert_eq!(
      Posit::<4, 1, i8>::cases_exhaustive_all().collect::<Vec<_>>().as_slice(),
      [
        Posit::from_bits(0b0000),
        Posit::from_bits(0b1000),
        Posit::from_bits(0b0001),
        Posit::from_bits(0b0010),
        Posit::from_bits(0b0011),
        Posit::from_bits(0b0100),
        Posit::from_bits(0b0101),
        Posit::from_bits(0b0110),
        Posit::from_bits(0b0111),
        Posit::from_bits(0b1111),
        Posit::from_bits(0b1110),
        Posit::from_bits(0b1101),
        Posit::from_bits(0b1100),
        Posit::from_bits(0b1011),
        Posit::from_bits(0b1010),
        Posit::from_bits(0b1001),
      ]
    )
  }

  #[test]
  fn decoded_cases_exhaustive() {
    let max_exp = 3 * (2 << 1);
    let n_frac = 1 << 7;
    assert_eq!(
      Decoded::<4, 1, i8>::cases_exhaustive().collect::<Vec<_>>().len(),
      (2 * max_exp + 1) * n_frac,
    );

    let exhaustive = Decoded::<4, 1, i8>::cases_exhaustive();
    let expected = (-12 ..= 12).flat_map(|exp| {
      (0b01_000000 ..= 0b01_111111).chain(0b10_000000u8 as i8 ..= 0b10_111111u8 as i8)
        .map(move |frac| Decoded{frac, exp})
    });
    assert!(exhaustive.eq(expected))
  }

  #[test]
  fn posit_6_2() {
    use malachite::rational::Rational;
    // Assert that `posit_6_2()` contains all posits
    assert_eq!(
      super::posit_6_2().map(|(posit, _)| posit).collect::<Vec<_>>().as_slice(),
      Posit::<6, 2, i32>::cases_exhaustive().collect::<Vec<_>>().as_slice(),
    );
    // And that the decoded values are correct
    for (posit, decoded) in super::posit_6_2() {
      assert_eq!(Rational::try_from(posit), Ok(Rational::from(decoded)))
    }
  }
}
