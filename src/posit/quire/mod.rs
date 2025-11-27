use super::*;

/// A *quire*, for a posit type with `N` bits and `ES` exponent bits, which is `SIZE` bytes long.
///
/// A quire is a fixed-point accumulator that enables sums and dot products of posits to be
/// calculated with **no** intermediate rounding whatsoever. This has tremendous practical uses,
/// from solving systems of equations to evaluating neural networks.
///
/// The `SIZE` is bounded from below based on the minimum size necessary to hold the product of two
/// posits. Above this, the more extra space, the more terms can be accumulated without the risk
/// of overflow (in practice the standard suggests ≈30 extra bits, corresponding to over a billion
/// terms). It is also required to be a multiple of 8 (64 bits) for performance reasons
/// (this requirement will be relaxed in the future).
///
/// If the quire `SIZE` is smaller than [the minimum size](Quire::MIN_SIZE) necessary for an `N`
/// bit posit with `ES` exponent bits, or if that size is not a multiple of 8, a **compilation
/// error** is raised.
///
/// Type aliases are provided at the [crate root](crate#types) for the quire types defined in
/// [the standard](https://posithub.org/docs/posit_standard-2.pdf#subsection.3.1).
///
/// # Example
///
/// ```
/// # use fast_posit::{p16, q16, Quire, RoundFrom, RoundInto};
/// // A 256-bit (32-byte) quire for a posit with 16 bits and 1 exponent bit
/// type Foo = Quire<16, 1, 32>;
///
/// // Compute sums and products in the quire with *no* loss of precision.
/// let mut quire = q16::ZERO;
/// quire += p16::MAX;
/// quire += p16::round_from(0.1);
/// quire -= p16::MAX;
/// let result: p16 = (&quire).round_into();  // Only the final step rounds
///
/// // Correct result with the quire, no issues with rounding errors.
/// assert_eq!(result, p16::round_from(0.1));
///
/// // The same sum without the quire would give a wrong result, due to double rounding.
/// let posit = (p16::MAX + p16::round_from(0.1)) - p16::MAX;
/// assert_eq!(posit, p16::ZERO);
/// ```
//
// The quire is represented as an array of bytes in little-endian order.
//
// It is also aligned to 128 bits, and we restrict `SIZE` to be a multiple of 64-bits (8 bytes).
// This allows many operations to be done in fixed-size increments of 64 bits. For small quires
// especially, this is extremely good for performance!
#[derive(Clone, Hash)]
#[repr(align(16))]
pub struct Quire<
  const N: u32,
  const ES: u32,
  const SIZE: usize,
> (pub(crate) [u8; SIZE]);

/// Basic constants and functions, such as the position of the fixed point, compile-time checks
/// that `SIZE` is ≥ the minimum size, etc.
mod basics;

/// Here is the core algorithm of the quire: adding the product of two posits, as a fixed-point
/// number, to the quire.
mod accumulate;

/// The user-facing functions live here: `+=`, `-=`, `add_prod`, `sub_prod`.
mod ops;

/// [Quire] -> [Posit] and [Posit] -> [Quire].
mod convert;
