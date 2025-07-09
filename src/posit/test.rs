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

  /// A [proptest Strategy](proptest::strategy::Strategy) that yields posits except 0 and NaR.
  pub(crate) fn cases_proptest() -> impl proptest::strategy::Strategy<Value = Self> {
    use proptest::prelude::*;
    (any::<bool>(), Self::RANGE_ABS).prop_map(|(sign, abs)| {
      let bits = if sign {abs} else {-abs};
      Self::from_bits(const_i128_as_int(bits))
    })
  }

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
}
