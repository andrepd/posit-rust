use super::*;

impl<
  const N: u32,
  const ES: u32,
  const SIZE: usize,
> Quire<N, ES, SIZE> {
  /// The core algorithm of the quire: adding a fixed-point number, represented as an array of
  /// `limbs` in big-endian order, shifted `offset` bytes from the right, and sign-extended to the
  /// size of the quire, to `self`.
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
  /// `limbs.len() * size_of::<Int>() + offset < SIZE` must hold, or calling this function
  /// is *undefined behaviour*.
  pub(crate) unsafe fn accumulate<const L: usize, Int: crate::Int>(
    &mut self,
    limbs: [Int; L],
    offset: usize,
  ) {
    // The `accumulate` function has three parts:
    //
    //   - We need to add (with carry) the `limbs` to the quire.
    //   - Then we need to propagate any carry that might exist, up until the end of the quire.
    //   - Then we need to check if we overflow the quire sum limit (highly unlikely), in which
    //     case the result should be NaR.
    debug_assert!(core::mem::size_of_val(&limbs) + offset < SIZE);

    // Add the `limbs` with carry.
    //
    // SAFETY: As a precondition, `offset < SIZE`, so `ptr` is in bounds of the array. But more
    // strongly, `offset + L * size_of::<Int>() < SIZE`, so `ptr` will _remain_ in bounds
    // throughout this loop. Finally, the `offset` is guaranteed to be aligned to `Int`, and so is
    // the quire itself (which is aligned to 128 bits). Therefore: the `src` and `dst` pointers
    // are always in bounds and aligned to `Int`.
    //
    // The following snippet seems to have great codegen: the fixed-size loop of `carrying_add`s is
    // actually compiled to a sequence of `adc` instructions on x86!
    let base_dst = unsafe { self.0.as_mut_ptr_range().end.byte_sub(offset) } as *mut Int;
    let base_src = limbs.as_ptr_range().end as *mut Int;
    let mut carry = false;
    for i in 0..L {
      let dst = unsafe { base_dst.sub(1 + i) };
      let src = unsafe { base_src.sub(1 + i) };
      let (result, overflow) = unsafe { Int::carrying_add((*dst).from_be(), (*src), carry)};
      unsafe { *dst = result.to_be() };
      carry = overflow;
    }

    // We're done with the limbs. Now the only value that needs to be "added" is an eventual carry
    // and/or sign bit, i.e. a value of +1, 0, or -1. This needs to be propagated until the end.
    let upper_padding = limbs[0] >> (Int::BITS - 1);
    let mut dst = unsafe { base_dst.sub(1 + L) };
    while dst as *const u8 >= self.0.as_ptr() {
      /*if !carry { return }*/
      let (result, overflow) = unsafe { (*dst).from_be().carrying_add(upper_padding, carry) };
      unsafe { *dst = result.to_be() }
      carry = overflow;
      dst = unsafe { dst.sub(1) }
    }

    /*// If we reach this, then would still be a carry beyond the limits of the quire. In this
    // (very unlikely) case, we set the quire to NaR.
    if carry == Int::ZERO { return }
    *self = Self::NAR*/

    // TODO: overflows of the quire sum limit should go to NaR!
  }

  /// Adding a [`Decoded`] to an existing [`Quire`].
  ///
  /// # Safety
  ///
  /// `x` must be the result of a [`Posit::decode_regular`] call, or calling this function
  /// is *undefined behaviour*.
  pub(crate) unsafe fn accumulate_decoded<Int: crate::Int>(&mut self, x: Decoded<N, ES, Int>) {
    debug_assert!(x.exp <= Posit::<N, ES, Int>::MAX_EXP + Int::ONE);

    // The quire is a fixed-point accumulator wide enough to accomodate the product of any two
    // posits (i.e. exponents from 2×MIN_EXP to 2×MAX_EXP), plus a number of carry bits.
    //
    // Accumulating a decoded is easy: we just take the `frac` and shift it `exp` places from the
    // fixed point, which is `WIDTH` places from the right. Positive `exp`s mean the `frac` is
    // shifted left of the fixed point, negative `exp`s mean the `frac` is shifted right of the
    // fixed point.
    //
    // TODO: if `WIDTH` is small enough, then `shift` could be negative. In this case, we have to
    // shift right by the inverse amount.
    let shift = (Int::of_u32(Self::WIDTH - Decoded::<N, ES, Int>::FRAC_WIDTH) + x.exp).as_u32();
    let (hi, lo, offset) = x.frac.multiword_shl(shift);

    // SAFETY: `x.exp` is between `MIN_EXP` and `MAX_EXP`, so the `offset` is always `< SIZE / 2`.
    unsafe { self.accumulate([hi, lo], offset) }
  }
}
