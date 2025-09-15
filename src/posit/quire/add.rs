use super::*;

impl<
  const N: u32,
  const ES: u32,
  const SIZE: usize,
> Quire<N, ES, SIZE> {
  /// The core algorithm of the quire: adding a [`Decoded`], which represents a product of two
  /// posits, to an existing [`Quire`].
  ///
  /// # Safety
  ///
  /// `x.exp` must be between `2 * Posit::<N, ES, Int>::MIN_EXP` and
  /// `2 * Posit::<N, ES,Int>::MAX_EXP`, otherwise calling this function is *undefined behaviour*.
  pub(crate) unsafe fn accumulate<Int: crate::Int>(&mut self, x: Decoded<N, ES, Int>) {
    // TODO only works for sums, not products, which need a double-precision `frac`.

    // The quire is a fixed-point accumulator wide enough to accomodate the product of any two
    // posits (i.e. exponents from 2×MIN_EXP to 2×MAX_EXP), plus a number of carry bits.
    //
    // Accumulating a decoded is easy: we just take the `frac` and shift it `exp` places from the
    // fixed point, which is `WIDTH` places from the right. Positive `exp`s mean the `frac` is
    // shifted left of the fixed point, negative `exp`s mean the `frac` is shifted right of the
    // fixed point.
    let shift = (Int::of_u32(Self::WIDTH - Decoded::<N, ES, Int>::FRAC_WIDTH) + x.exp).as_u32();
    let (hi, lo, offset) = x.frac.multiword_shl(shift);

    // Add the `lo` and `hi` bytes with carry.
    //
    // SAFETY: `x.exp` is between `2 * MIN_EXP` and `2 * MAX_EXP`, so the `offset` is always in
    // bounds of `0 ≤ offset < SIZE`. Furthermore, the `offset` is guaranteed to be aligned to
    // `Int`, and so is the quire itself (which is aligned to 128 bits). Therefore the pointers
    // are in bounds and aligned to `Int`.
    use crate::underlying::Unsigned;
    let end_ptr = unsafe { self.0.as_mut_ptr_range().end.sub(offset) } as *mut Int;
    let lo_ptr = unsafe { end_ptr.sub(1) } as *mut Int::Unsigned;
    let hi_ptr = unsafe { lo_ptr.sub(1) } as *mut Int;

    let (lo_result, overflow) = unsafe { (*lo_ptr).overflowing_add(lo.to_be()) };
    unsafe { *lo_ptr = lo_result }

    let (hi_result, overflow) = unsafe { (*hi_ptr).carrying_add(hi.to_be(), overflow) };
    unsafe { *hi_ptr = hi_result }

    // Only these two words have actual numbers that need to be added. From now on, there's only a
    // carry of +1, 0, or -1 that needs to be propagated until the end.
    let mut carry = Int::from(overflow).wrapping_sub(Int::from(!x.frac.is_positive()));
    let mut ptr = unsafe { hi_ptr.sub(1) };
    while ptr as *const u8 >= self.0.as_ptr() {
      if carry == Int::ZERO { return }
      let (result, overflow) = unsafe { (*ptr).overflowing_add(carry) };
      unsafe { *ptr = result }
      carry = Int::from(overflow).wrapping_sub(Int::from(!x.frac.is_positive()));
      ptr = unsafe { ptr.sub(1) }
    }

    /*// If we reach this, then would still be a carry beyond the limits of the quire. In this
    // (very unlikely) case, we set the quire to NaR.
    if carry == Int::ZERO { return }
    *self = Self::NAR*/

    // TODO: overflows of the quire sum limit should go to NaR!
  }
}
