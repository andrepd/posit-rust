use super::*;

/// A *quire*, for a posit type with `N` bits and `ES` exponent bits, which is `SIZE` bytes long.
///
/// A quire is a fixed-point accumulator that enables sums and dot products of posits to be
/// calculated with **no** intermediate rounding whatsoever. This has tremendous practical uses,
/// from solving systems of equations to evaluating neural networks.
///
/// The `SIZE` is bounded from below based on the minimum size necessary to hold the product of two
/// posits (smaller `SIZE`s are a compile-time error). Above this, the more extra space, the more
/// terms can be accumulated without the risk of overflow (in practice the standard suggests ≈30
/// extra bits, corresponding to over a billion terms).
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
// It is also aligned to 64 bits, and we restrict `SIZE` to be a multiple of 64-bits (8 bytes).
#[repr(align(8))]
pub struct Quire<
  const N: u32,
  const ES: u32,
  const SIZE: usize,
> (pub(crate) [u8; SIZE]);

/// Basic constants and functions, such as the position of the fixed point, compile-time checks
/// that `SIZE` is ≥ the minimum size, etc.
mod basics;
