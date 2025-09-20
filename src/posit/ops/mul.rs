use super::*;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  /// Return a [normalised](Decoded::is_normalised) `Decoded` that's the result of multiplying `x`
  /// and `y`, plus the sticky bit.
  ///
  /// # Safety
  ///
  /// `x` and `y` have to be [normalised](Decoded::is_normalised), or calling this function
  /// is *undefined behaviour*.
  #[inline]
  pub(crate) unsafe fn mul_kernel(x: Decoded<N, ES, Int>, y: Decoded<N, ES, Int>) -> (Decoded<N, ES, Int>, Int) {
    // Multiplying two numbers in the form `frac × 2^exp` is much easier than adding them. We have
    //
    //   (x.frac / FRAC_DENOM * 2^x.exp) * (y.frac / FRAC_DENOM * 2^y.exp)
    //   = (x.frac * y.frac) / FRAC_DENOM² * 2^(x.exp + y.exp)
    //   = (x.frac * y.frac / FRAC_DENOM) / FRAC_DENOM * 2^(x.exp + y.exp)
    //
    // In other words: the resulting `exp` is just the sum of the `exp`s, and the `frac` is the
    // product of the `frac`s divided by `FRAC_DENOM`. Since we know `FRAC_DENOM` = `2^FRAC_WIDTH`
    // = `2^(Int::BITS - 2)`, we can re-arrange the expression one more time:
    //
    //   = (x.frac * y.frac / 2^FRAC_WIDTH) / FRAC_DENOM * 2^(x.exp + y.exp)
    //   = ((x.frac * y.frac) >> Int::BITS) / FRAC_DENOM * 2^(x.exp + y.exp + 2)
    //
    // Meaning the result has
    //
    //   frac = (x.frac * y.frac) >> Int::BITS
    //    exp = x.exp + y.exp + 2
    //
    // Only a couple other points to keep in mind:
    //
    //   - The multiplication must use a type with double the precision of `Int`, so that there is
    //     no chance of overflow.
    //   - When we shift the frac right by `Int::BITS`, we must also accumulate the lower
    //     `Int::BITS` to `sticky`.
    //   - The `frac` must start with `0b01` or `0b10`, i.e. it must represent a `frac` in the
    //     range [1., 2.[ or [-2., 1.[, but the result of multiplying the `frac`s may not. When
    //     that happens, we may need to shift 1 or 2 places left. For example: 1. × 1. = 1., but
    //     1.5 × 1.5 = 2.25; the former is good, the latter needs an extra shift by 1 to become
    //     1.125. Of course, if we shift the `frac` left by n places we must subtract n from `exp`.
    //
    // Keeping these points in mind, the final result is
    //
    //   frac = (x.frac * y.frac) << underflow >> Int::BITS
    //    exp = x.exp + y.exp + 2 - underflow

    use crate::underlying::Double;
    let mul = x.frac.doubling_mul(y.frac);
    // SAFETY: `x.frac` and `y.frac` are not 0, so their product cannot be 0; nor can it ever be MIN
    let underflow = unsafe { mul.leading_run_minus_one() };  // Can only be 0,1,2, optimise?
    let (frac, sticky) = (mul << underflow).components_hi_lo();
    let exp = x.exp + y.exp + Int::ONE + Int::ONE - Int::of_u32(underflow);

    (Decoded{frac, exp}, sticky)
  }

  pub(crate) fn mul(self, other: Self) -> Self {
    if self == Self::NAR || other == Self::NAR {
      Self::NAR
    } else if self == Self::ZERO || other == Self::ZERO {
      Self::ZERO
    } else {
      // SAFETY: neither `self` nor `other` are 0 or NaR
      let a = unsafe { self.decode_regular() };
      let b = unsafe { other.decode_regular() };
      // SAFETY: `self` and `other` aren't symmetrical
      let (result, sticky) = unsafe { Self::mul_kernel(a, b) };
      // SAFETY: `result.is_normalised()` holds
      unsafe { result.encode_regular_round(sticky) }
    }
  }
}

use core::ops::{Mul, MulAssign};
super::mk_ops!{Mul, MulAssign, mul, mul_assign}

#[cfg(test)]
mod tests {
  super::mk_tests!{*, *=}
}
