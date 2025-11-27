use super::*;

use crate::fallthrough;
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
  /// The core algorithm of the quire: adding a fixed-point number, represented as an array of
  /// `limbs` in little-endian order, shifted `offset` bytes from the right, and sign-extended to
  /// the size of the quire, to `self`.
  ///
  /// In other words, the "logical" number to add to the quire is `limbs`, padded with `offset`
  /// bits on the right equal to 0, and infinite bits on the left equal to the msb of bytes.
  ///
  /// E.g. if `limbs = [0b1101, 0b0111]`, the logical value would be
  ///
  /// ```text
  /// …11,1111,1111|1101,0111|0000,00…
  ///             ^   ^       ^
  ///   msb padding   limbs   0 padding
  /// ```
  ///
  /// # Safety
  ///
  /// `limbs.len() * size_of::<Int>() + offset ≤ SIZE` must hold, or calling this function
  /// is *undefined behaviour*.
  ///
  /// # Visual example:
  ///
  /// ```text
  /// self   = [self[0], self[1], self[2], self[3], self[4], self[6], self[6], self[7]]
  /// limbs  =                           [limbs[0], limbs[1]]
  /// offset = 3
  /// ```
  ///
  /// then the result is the result of adding the little-endian bignums
  ///
  /// ```text
  /// [self[0], self[1], self[2], self[3] , self[4] , self[5] , self[6] , self[7] ]
  /// [0      , 0      , 0      , limbs[0], limbs[1], implicit, implicit, implicit]
  /// ```
  ///
  /// where `implicit = if limbs[1] ≥ 0 {0} else {-1}`.
  /*#[inline(always)]*/  // TODO Unclear: benefits round_from(posit) by 30% but worsens += posit by 70%
  pub(crate) unsafe fn accumulate<const L: usize>(
    &mut self,
    limbs: &[u64; L],
    offset: usize,
  ) {
    let quire: &mut [u64] = self.as_u64_array_mut();
    let len_u64 = quire.len();

    if cfg!(debug_assertions) {
      debug_assert!(offset + limbs.len() <= quire.len())
    } else {
      // SAFETY: Precondition.
      unsafe { core::hint::assert_unchecked(offset + limbs.len() <= quire.len()) }
    }

    // Part 1: Add `limbs[..]` to `quire[offset .. offset + L]`.
    let mut carry = false;
    for i in 0 .. limbs.len() {
        // SAFETY: This follows from the above precondition, but we re-assert it to help the
        // compiler.
        unsafe { core::hint::assert_unchecked(offset + i < quire.len()) }
        let (r, o) = u64::carrying_add(quire[offset + i], limbs[i], carry);
        quire[offset + i] = r;
        carry = o;
    }

    // In principle the compiler is able to optimise this, but just in case...
    if const { L == Self::SIZE / 8 } { return }

    // Part 2: Add `implicit` to `quire[offset + L ..]`.
    let implicit = (limbs[L-1] as i64 >> 63) as u64;

    fallthrough!(offset + limbs.len(),
               0 => if  0 < len_u64 { let (r,o) = u64::carrying_add(quire[ 0], implicit, carry); quire[ 0] = r; carry = o; },
        'l1:   1 => if  1 < len_u64 { let (r,o) = u64::carrying_add(quire[ 1], implicit, carry); quire[ 1] = r; carry = o; },
        'l2:   2 => if  2 < len_u64 { let (r,o) = u64::carrying_add(quire[ 2], implicit, carry); quire[ 2] = r; carry = o; },
        'l3:   3 => if  3 < len_u64 { let (r,o) = u64::carrying_add(quire[ 3], implicit, carry); quire[ 3] = r; carry = o; },
        'l4:   4 => if  4 < len_u64 { let (r,o) = u64::carrying_add(quire[ 4], implicit, carry); quire[ 4] = r; carry = o; },
        'l5:   5 => if  5 < len_u64 { let (r,o) = u64::carrying_add(quire[ 5], implicit, carry); quire[ 5] = r; carry = o; },
        'l6:   6 => if  6 < len_u64 { let (r,o) = u64::carrying_add(quire[ 6], implicit, carry); quire[ 6] = r; carry = o; },
        'l7:   7 => if  7 < len_u64 { let (r,o) = u64::carrying_add(quire[ 7], implicit, carry); quire[ 7] = r; carry = o; },
        'l8:   8 => if  8 < len_u64 { let (r,o) = u64::carrying_add(quire[ 8], implicit, carry); quire[ 8] = r; carry = o; },
        'l9:   9 => if  9 < len_u64 { let (r,o) = u64::carrying_add(quire[ 9], implicit, carry); quire[ 9] = r; carry = o; },
        'l10: 10 => if 10 < len_u64 { let (r,o) = u64::carrying_add(quire[10], implicit, carry); quire[10] = r; carry = o; },
        'l11: 11 => if 11 < len_u64 { let (r,o) = u64::carrying_add(quire[11], implicit, carry); quire[11] = r; carry = o; },
        'l12: 12 => if 12 < len_u64 { let (r,o) = u64::carrying_add(quire[12], implicit, carry); quire[12] = r; carry = o; },
        'l13: 13 => if 13 < len_u64 { let (r,o) = u64::carrying_add(quire[13], implicit, carry); quire[13] = r; carry = o; },
        'l14: 14 => if 14 < len_u64 { let (r,o) = u64::carrying_add(quire[14], implicit, carry); quire[14] = r; carry = o; },
        'l15: 15 => if 15 < len_u64 { let (r,o) = u64::carrying_add(quire[15], implicit, carry); quire[15] = r; carry = o; },
        'z: _ => return,
    );

    // TODO: overflows of the quire sum limit should go to NaR!
  }

  /// Adding a [`Decoded`] to an existing [`Quire`].
  ///
  /// # Safety
  ///
  /// `x` must be the result of a [`Posit::decode_regular`] call, or calling this function
  /// is *undefined behaviour*.
  pub(crate) unsafe fn accumulate_decoded<Int: crate::Int>(&mut self, x: Decoded<N, ES, Int>) {
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
    if base_shift <= Posit::<N, ES, Int>::MAX_EXP
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
      let (hi, lo, offset) = multiword_shl_64(x.frac, shift_left);

      // Another edge case: we check in `Self::MIN_SIZE` that we have enough bits. But if we have
      // less than 64 to spare, then the `hi` word might be pushed out of the quire. In this case,
      // we must be careful to **not** add `&[lo, hi]`, but just `&[lo]`, or we would write out of
      // bounds.
      //
      // Note that again, like the previous edge case above, this only happens on a small portion
      // of types (e.g. among the standard types only on p8 and q8), and for types where it cannot
      // happen the branch is not even included in the binary.
      if Self::WIDTH + 2 + Posit::<N, ES, Int>::MAX_EXP.as_u32() > Self::BITS - 64 
      && offset == Self::SIZE / 8 - 1 {
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
