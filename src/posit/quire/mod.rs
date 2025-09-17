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
/// If the quire `SIZE` is smaller than [the minimum size](Quire::MIN_SIZE), or if it is not a
/// multiple of 8, a **compilation error** is raised.
///
/// # Examples
///
/// ```
/// // TODO
/// ```
//
// The quire is represented as an array of bytes in big-endian order. This is because (we theorise
// at the moment, with no data) since most operations need to start by checking if the most
// significant byte is NaR (= 0b10000000), placing that byte first is the best layout for cache.
//
// On the other hand, adding with carry is more natural to do in little-endian order, and also
// avoids the work of shuffling bits from little-endian to big-endian in little-endian
// architectures... Need to try and profile.
//
// It is also aligned to 128 bits, and we restrict `SIZE` to be a multiple of 64-bits (8 bytes).
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
mod add;

/// The user-facing functions live here: `+=`, `-=`, `add_prod`, `sub_prod`.
mod ops;

/// [Quire] -> [Posit] and [Posit] -> [Quire].
mod convert;
