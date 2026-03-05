use super::*;

use crate::underlying::const_as;

/// Aux function: adapter for `Int::multiword_shl<64>`.
///
/// Compute the result of a multiword left-shift. The return value is `(hi, lo, shift_words)`, such
/// that, in terms of infinite precision arithmetic:
///
/// ```ignore
/// self << n = (hi << Self::BITS + lo) << (shift_words * 64)
/// ```
fn multiword_shl_64<Int: crate::Int>(x: Int, n: u32) -> (u64, u64, usize) {
  use crate::underlying::Sealed;
  let x = const_as::<Int, i64>(x);
  let (hi, lo, offset_bits) = x.multiword_shl::<64>(n);
  let offset_bytes = offset_bits as usize / 64;
  (hi as u64, lo as u64, offset_bytes)
}

impl<
  const N: u32,
  const ES: u32,
  const SIZE: usize,
> Quire<N, ES, SIZE> {
  /// Adding a [`Decoded`] to an existing [`Quire`].
  ///
  /// # Safety
  ///
  /// `x` must be the result of a [`Posit::decode_regular`] call, or calling this function
  /// is *undefined behaviour*.
  /*#[inline(always)]*/
  pub(crate) unsafe fn add_posit_kernel<Int: crate::Int>(&mut self, x: Decoded<N, ES, Int>) {
    const { assert!(Int::BITS <= 64, "Quire operations are currently not supported for N > 64") };
    debug_assert!(x.exp.abs() <= Posit::<N, ES, Int>::MAX_EXP + Int::ONE);

    // The quire is a fixed-point accumulator wide enough to accomodate the product of any two
    // posits (i.e. exponents from 2×MIN_EXP to 2×MAX_EXP), plus a number of carry bits.
    //
    // Accumulating a Decoded is easy: we just take the `frac` and shift it `exp` places from the
    // fixed point, which is `WIDTH` places from the right. Positive `exp`s mean the `frac` is
    // shifted left of the fixed point, negative `exp`s mean the `frac` is shifted right of the
    // fixed point.
    //
    // Writing `base_shift` as `WIDTH - FRAC_WIDTH`: we need to shift by `base_shift + x.exp`.
    let base_shift = Int::of_u32(Self::WIDTH) - Int::of_u32(Decoded::<N, ES, Int>::FRAC_WIDTH);
    let shift = base_shift + x.exp;

    // One caveat: even though `shift` is almost always positive (a left-shift), if `FRAC_WIDTH` is
    // wide enough, then `shift` might be negative and we might actually need to shift the `frac`
    // right, not left.
    //
    // To ensure we do not do an extra branch when this is guaranteed not to happen (which is the
    // case for most "reasonable" types, including standard types), we place this branch behind an
    // `if const` (well, not quite because of limitations in Rust, but yes, `base_shift` is a
    // constant and will be folded out). We simply check if `base_shift - MAX_EXP` can ever be
    // negative (a right-shift). If not, this branch is not even included in the binary.
    if /*const*/ { base_shift <= Posit::<N, ES, Int>::MAX_EXP }
    && shift < Int::ZERO {
      // Note: no bits of `frac` are actually lost in the right-shift; this is just because `Int`
      // itself is wide enough relative to `N` and `ES`.
      let shift_right = (-shift).as_u32();
      debug_assert_eq!(x.frac.mask_lsb(shift_right), Int::ZERO);
      // SAFETY: `limbs` is only one `Int`, and `offset` is `0`.
      let lo = const_as::<Int, i64>(x.frac) >> shift_right;
      unsafe { self.accumulate(&[lo as u64], 0) }
    }

    // Normal case: we multiword-shift left by `shift_left` bits.
    else {
      let shift_left = shift.as_u32();
      // dbg!(x.frac, shift_left);
      let (hi, lo, offset) = multiword_shl_64(x.frac, shift_left);

      // Another edge case: we check in `Self::MIN_SIZE` that we have enough bits. But if we have
      // less than 64 to spare, then the `hi` word might be pushed out of the quire. In this case,
      // we must be careful to **not** add `&[lo, hi]`, but just `&[lo]`, or we would write out of
      // bounds.
      //
      // Note that again, like the previous edge case above, this only happens on a small portion
      // of types (e.g. among the standard types only on p8 and q8), and for types where it cannot
      // happen the branch is not even included in the binary.
      if /*const*/ { Self::WIDTH + 2 + Posit::<N, ES, Int>::MAX_EXP.as_u32() > Self::BITS - 64 }
      && offset == const { Self::SIZE / 8 - 1 } {
        debug_assert!((lo as i64) >= 0 && hi as i64 == 0 || (lo as i64) < 0 && hi as i64 == -1 );
        unsafe { self.accumulate(&[lo], offset) }
      }

      // Otherwise, business as usual
      else {
        // SAFETY: `x.exp` is between `MIN_EXP` and `MAX_EXP`, so the `offset` is always `< SIZE / 2`.
        unsafe { self.accumulate(&[lo, hi], offset) }
      }
    }
  }
}
