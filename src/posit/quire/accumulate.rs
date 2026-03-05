use super::*;

use crate::fallthrough;

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
  /// `size_of::<[u64; L]>() + offset ≤ SIZE` must hold, or calling this function
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
  /*#[inline(always)]*/  // TODO Unclear: improves microbench round_from(posit) by ~30% but worsens += posit by ~70%...
  pub(crate) unsafe fn accumulate<const L: usize>(
    &mut self,
    limbs: &[u64; L],
    offset: usize,
  ) {
    unsafe { self.accumulate_slice(limbs.as_slice(), offset) }
  }

  /*#[inline(always)]*/
  pub(crate) unsafe fn accumulate_slice(
    &mut self,
    limbs: &[u64],
    offset: usize,
  ) {
    let quire: &mut [u64] = self.as_u64_array_mut();
    let len_u64 = quire.len();
    let original_sign = quire[len_u64 - 1];

    if cfg!(debug_assertions) {
      debug_assert!(offset + limbs.len() <= len_u64)
    } else {
      // SAFETY: Precondition.
      unsafe { core::hint::assert_unchecked(offset + limbs.len() <= len_u64) }
    }

    // Part 1: Add `limbs[..]` to `quire[offset .. offset + L]`.
    let mut carry = false;
    for i in 0 .. limbs.len() {
        // SAFETY: This follows from the above precondition, but we re-assert it to help the
        // compiler.
        unsafe { core::hint::assert_unchecked(offset + i < len_u64) }
        let (r, o) = u64::carrying_add(quire[offset + i], limbs[i], carry);
        quire[offset + i] = r;
        carry = o;
    }

    // Part 2: Add `implicit` to `quire[offset + L ..]`.
    let implicit = (limbs[limbs.len()-1] as i64 >> 63) as u64;

    // One line of the jump table below
    macro_rules! jump_table_line {
      ($n:literal) => {
        if $n < len_u64 {
          let (r,o) = u64::carrying_add(quire[$n], implicit, carry);
          quire[$n] = r;
          carry = o;
        }
      };
    }

    fallthrough!(offset + limbs.len(),
               0 => jump_table_line!( 0),
        'l1:   1 => jump_table_line!( 1),
        'l2:   2 => jump_table_line!( 2),
        'l3:   3 => jump_table_line!( 3),
        'l4:   4 => jump_table_line!( 4),
        'l5:   5 => jump_table_line!( 5),
        'l6:   6 => jump_table_line!( 6),
        'l7:   7 => jump_table_line!( 7),
        'l8:   8 => jump_table_line!( 8),
        'l9:   9 => jump_table_line!( 9),
        'l10: 10 => jump_table_line!(10),
        'l11: 11 => jump_table_line!(11),
        'l12: 12 => jump_table_line!(12),
        'l13: 13 => jump_table_line!(13),
        'l14: 14 => jump_table_line!(14),
        'l15: 15 => jump_table_line!(15),
        'z: _ => (),
    );

    // Part 3: If the quire originally had the same sign as `limbs`, but now has a different sign,
    // there was overflow.
    if ((original_sign ^ implicit) as i64) > 0
    && ((quire[len_u64 - 1] ^ implicit) as i64) < 0 {
      *self = Self::NAR
    }
  }
}
