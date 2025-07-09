//! Simple functions of 1 argument

use super::*;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  /// Returns the posit value of the lexicographic successor of `self`'s representation.
  ///
  /// **Standard:** "next".
  pub fn next(self) -> Self {
    Self::from_bits(self.0.wrapping_add(Int::ONE))
  }

  /// Returns the posit value of the lexicographic predecessor of `self`'s representation.
  ///
  /// **Standard:** "prior".
  pub fn prior(self) -> Self {
    Self::from_bits(self.0.wrapping_sub(Int::ONE))
  }
}
