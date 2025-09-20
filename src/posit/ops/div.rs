use super::*;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Posit<N, ES, Int> {
  /// Return a [normalised](Decoded::is_normalised) `Decoded` that's the result of dividing `x` by
  /// `y`, plus the sticky bit.
  ///
  /// # Safety
  ///
  /// `x` and `y` have to be [normalised](Decoded::is_normalised), or calling this function
  /// is *undefined behaviour*.
  #[inline]
  pub(crate) unsafe fn div_kernel(x: Decoded<N, ES, Int>, y: Decoded<N, ES, Int>) -> (Decoded<N, ES, Int>, Int) {
    // Let's use ÷ to denote true mathematical division, and / denote integer division *that rounds
    // down* (i.e. towards negative infinity, not towards zero). To divide two numbers in the form
    // `frac × 2^exp`, we have:
    //
    //   (x.frac ÷ FRAC_DENOM * 2^x.exp) ÷ (y.frac ÷ FRAC_DENOM * 2^y.exp)
    //   = (x.frac ÷ y.frac) * 2^(x.exp - y.exp)
    //   = (x.frac ÷ y.frac * FRAC_DENOM) ÷ FRAC_DENOM * 2^(x.exp - y.exp)
    //
    // Since we know `FRAC_DENOM` = `2^FRAC_WIDTH`, we can re-arrange the expression one more
    // time:
    //
    //   = (x.frac ÷ y.frac * 2^FRAC_WIDTH) ÷ FRAC_DENOM * 2^(x.exp - y.exp)
    //   = ((x.frac ÷ y.frac) << FRAC_WIDTH) ÷ FRAC_DENOM * 2^(x.exp - y.exp)
    //   = ((x.frac << FRAC_WIDTH) / y.frac) ÷ FRAC_DENOM * 2^(x.exp - y.exp)
    //
    // Meaning the result has
    //
    //   frac = (x.frac << FRAC_WIDTH) / y.frac
    //    exp = x.exp - y.exp
    //
    // But this is not quite correct. This is because `(x.frac << FRAC_WIDTH) / y.frac` may
    // underflow, which means some bits will be lost at the end. To avoid this, we compute the
    // `underflow` first, then adjust the shift amount and the exponent accordingly.
    //
    //   frac = (x.frac << (FRAC_WIDTH + underflow)) / y.frac
    //    exp = x.exp - y.exp - underflow

    // TODO: The current implementation does two divisions, which is expensive. But the `underflow`
    // can really only be [0,1,2]. Maybe we can determine this by just looking at the signs and
    // relative magnitudes of the `frac`s, without dividing. Then we only need to do the second
    // division.
    let (div, _) = x.frac.shift_div_rem(y.frac, Decoded::<N, ES, Int>::FRAC_WIDTH);
    // SAFETY: `x.frac` and `y.frac` are not 0, so `div` cannot be 0; nor can it ever be MIN
    let underflow = unsafe { div.leading_run_minus_one() };

    let (frac, sticky) = x.frac.shift_div_rem(y.frac, Decoded::<N, ES, Int>::FRAC_WIDTH + underflow);
    let exp = x.exp - y.exp - Int::of_u32(underflow);

    (Decoded{frac, exp}, sticky)
  }

  pub(crate) fn div(self, other: Self) -> Self {
    if self == Self::NAR || other == Self::NAR || other == Self::ZERO {
      Self::NAR
    } else if self == Self::ZERO {
      Self::ZERO
    } else {
      // SAFETY: neither `self` nor `other` are 0 or NaR
      let a = unsafe { self.decode_regular() };
      let b = unsafe { other.decode_regular() };
      let (result, sticky) = unsafe { Self::div_kernel(a, b) };
      // SAFETY: `result.is_normalised()` holds
      unsafe { result.encode_regular_round(sticky) }
    }
  }
}

use core::ops::{Div, DivAssign};
super::mk_ops!{Div, DivAssign, div, div_assign}

#[cfg(test)]
mod tests {
  super::mk_tests!{/, /=}
}
