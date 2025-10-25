use super::*;

use crate::underlying::const_as;

/// The kernel for converting a _signed_ int to a posit.
///
/// # Safety
///
/// `int` cannot be `FromInt::ZERO` or `FromInt::MIN`, or calling this function is *undefined
/// behaviour*.
#[inline]
unsafe fn round_from_kernel<
  FromInt: crate::Int,
  const N: u32,
  const ES: u32,
  Int: crate::Int,
>(int: FromInt) -> (Decoded<N, ES, Int>, Int) {
  // If converting into a narrower type (`FromInt` → `Int`), we need to shift right, *before* we
  // convert to the narrower type. Some bits will be lost in this conversion; we will accumulate
  // them into `sticky`.
  let shift_right = if const { Int::BITS >= FromInt::BITS } {0} else {FromInt::BITS - Int::BITS};

  // If converting into a wider type (`FromInt` → `Int`), we need to shift left, *after* we convert
  // to the wider type.
  let shift_left = if const { Int::BITS <= FromInt::BITS } {0} else {Int::BITS - FromInt::BITS};

  // To turn the `int` into a `frac` that starts with `0b01` or `0b10`, find the number of leading
  // 0s or 1s, and shift left by that number of places minus one. To compensate, the `exp` has to
  // be `FRAC_WIDTH` subtracted by the number of places we shifted. The `sticky` bits are the bits
  // lost when shifting right.
  //
  // Examples:
  //
  //   value: 0b00010011 (= 19)
  //    frac: 0b01001100
  //     exp: +4 (= (8 - 2) frac width - 2 underflow)
  //
  //   value: 0b11111111 (= -1)
  //    frac: 0b10000000
  //     exp: -1 (= (8 - 2) frac width - 7 underflow)
  //
  // SAFETY: `int` is not 0 nor MIN (function precondition)
  let underflow = unsafe { int.leading_run_minus_one() };
  let frac = const_as::<FromInt, Int>(int << underflow >> shift_right) << shift_left;
  let exp = {
    let exp = Decoded::<N, ES, FromInt>::FRAC_WIDTH.wrapping_sub(underflow);
    const_as::<i32, Int>(exp as i32)
  };
  let sticky = {
    let true_shift = shift_right.saturating_sub(underflow);
    Int::from(int.mask_lsb(true_shift) != FromInt::ZERO)
  };

  (Decoded{frac, exp}, sticky)
}

/// The kernel for converting a posit to a _signed_ int.
#[inline]
fn round_into_kernel<
  ToInt: crate::Int,
  const N: u32,
  const ES: u32,
  Int: crate::Int,
>(decoded: Decoded<N, ES, Int>) -> ToInt {
  // If converting into a narrower type (`Int` → `ToInt`), we need to shift right, *before* we
  // convert to the narrower type. Some bits will be lost in this conversion; we will accumulate
  // them into `sticky`.
  let diff_right = if const { ToInt::BITS >= Int::BITS } {0} else {Int::BITS - ToInt::BITS};

  // If converting into a wider type (`Int` → `ToInt`), we may shift left, *after* we convert to
  // the wider type.
  let diff_left = if const { ToInt::BITS <= Int::BITS } {0} else {ToInt::BITS - Int::BITS};

  // To convert `decoded` into an int, note that the value it represents is
  //
  //   frac × 2^-FRAC_WIDTH × 2^exp
  //
  // The integer part of this is the result, the fractional part determines the direction of the
  // rounding (as always, the rounding is "round to nearest, ties to even"; to understand in more
  // detail how this is implemented using `round` and `sticky` bits, see the comments in
  // [`encode_regular_round`]).
  //
  // Examples:
  //
  //   19.0:
  //      frac: 0b01_001100
  //       exp: +4
  //     shift: 6 frac width - 4 exp = 2
  //     value: 0b00010011 = 19
  //
  //   -1.0:
  //      frac: 0b10_000000
  //       exp: -1 (= (8 - 2) frac width - 7 underflow)
  //     shift: 6 frac width + 1 exp = 7
  //     value: 0b11111111 = -1
  //
  //   19.5:
  //      frac: 0b01_001110
  //       exp: +4
  //     shift: 6 frac width - 4 exp = 2
  //     value: 0b00010100 = 20 (rounded up)
  //
  // Two points to keep in mind
  //
  //   - `ToInt` may be wider or narrower than the source posit's `Int`, so we must be careful in
  //     doing the shift and casts in the right order
  //   - The shift may be too big in either direction: if too big to the left it leads to overflow
  //     (in which case `ToInt::MIN` is returned), and if too big to the right it leads to loss of
  //     all bits (in which case `ToInt::ZERO` is returned).

  // This is the amount that `frac` needs to be shifted right (or left, if negative).
  let shift = Int::of_u32(Decoded::<N, ES, Int>::FRAC_WIDTH).wrapping_sub(decoded.exp);

  // If `shift` is negative: the `ToInt` type needs to be wide enough to hold the value.
  if shift < Int::ZERO {
    let shift_left = (-shift).as_u32();
    if shift_left > diff_left {
      // Too narrow, return `0b10000…`.
      return ToInt::MIN;
    }
    const_as::<Int, ToInt>(decoded.frac) << shift_left
  }
  // If `shift` is exactly zero: the `ToInt` type cannot be any narrower.
  else if shift == Int::ZERO {
    if diff_right != 0 {
      // Too narrow, return `0b10000…`.
      return ToInt::MIN;
    }
    const_as::<Int, ToInt>(decoded.frac)
  }
  // If `shift` is greater than zero: the `ToInt` type needs to be wide enough to hold the value;
  // also since we shift left we need to take care of rounding depending on what bits were lost.
  else {
    let shift_right = shift.as_u32();
    if shift_right > Int::BITS {
      // The whole thing is shifted out, return `0`.
      return ToInt::ZERO;
    }
    if shift_right < diff_right {
      // Too narrow, return `0b10000…`.
      return ToInt::MIN;
    }
    // Rounding formula with round bit and sticky bit, for details see [`encode_regular_round`].
    let sticky = decoded.frac.mask_lsb(shift_right - 1);
    let int = decoded.frac >> (shift_right - 1);
    let round = int.get_lsb();
    let int = int >> 1;
    let odd = int.get_lsb();
    // Assemble the number, with the rounding rules.
    //
    // One detail: we use wrapping_add on round_up because, if the rounded value exceeds
    // `ToInt::MAX`, when adding 1 we wrap around to `ToInt::MIN` = `0b1000…`, which is exactly
    // what we want (example: if `i8::MAX` == 127, but the posit is 127.5, rounding up to 128
    // exceeds the representable irange of `i8`, so we return `i8::MIN`).
    let round_up: bool = round & (odd | (sticky != Int::ZERO));
    const_as::<Int, ToInt>(int).wrapping_add(ToInt::from(round_up))
  }
}

macro_rules! make_impl {
  ($t:ty) => {
    impl<
      const N: u32,
      const ES: u32,
      Int: crate::Int,
    > RoundFrom<$t> for Posit<N, ES, Int> {
      #[doc = concat!("Convert an `", stringify!($t), "` into a `Posit`, [rounding according to the standard]:")]
      ///
      #[doc = concat!("  - If the value is [`", stringify!($t), "::MIN`] (i.e. the value where the most significant bit is 1 and the rest are 0), it converts to [NaR](Posit::NAR).")]
      ///   - Otherwise, the integer value is rounded (if necessary).
      ///
      /// [rounding according to the standard]: https://posithub.org/docs/posit_standard-2.pdf#subsection.6.4
      fn round_from(value: $t) -> Self {
        // Handle 0 and MIN. Remember that according to the standard, MIN (i.e. bit pattern
        // 0b1000…), is converted to NaR, and NaR is converted to MIN.
        if value == 0 { return Posit::ZERO }
        if value == <$t>::MIN { return Posit::NAR }

        // This piece of code is only necessary in really extreme cases, like converting i128::MAX
        // to an 8-bit posit. But in those cases, we do need to guard against overflow on `exp`.
        if const { <$t>::BITS as i128 > 1 << Decoded::<N, ES, Int>::FRAC_WIDTH } {
          let limit = 1 << (1 << Decoded::<N, ES, Int>::FRAC_WIDTH);
          if value >=  limit { return Posit::MAX }
          if value <= -limit { return Posit::MIN }
        }

        // SAFETY: `value` is not 0 or MIN
        let (result, sticky) = unsafe { round_from_kernel(value) };
        // SAFETY: `frac` is not underflowing and `exp` cannot be greater than `FromInt::BITS`
        unsafe { result.encode_regular_round(sticky) }
      }
    }

    impl<
      const N: u32,
      const ES: u32,
      Int: crate::Int,
    > RoundFrom<Posit<N, ES, Int>> for $t {
      #[doc = concat!("Convert a `Posit` into an `", stringify!($t), "`, [rounding according to the standard]:")]
      ///
      #[doc = concat!("  - If the value is [NaR](Posit::NAR), or if overflows the target type, then it converts to [`", stringify!($t), "::MIN`] (i.e. the value where the most significant bit is 1 and the rest are 0).")]
      ///   - Otherwise, it returns the nearest integer to `value`, rounding ties to even.
      ///
      /// [rounding according to the standard]: https://posithub.org/docs/posit_standard-2.pdf#subsection.6.4
      // TODO examples? here and in the other conversions
      fn round_from(value: Posit<N, ES, Int>) -> Self {
        if value == Posit::ZERO { return 0 }
        if value == Posit::NAR { return <$t>::MIN }

        // SAFETY: `value` is not 0 or NaR
        let decoded = unsafe { value.decode_regular() };
        round_into_kernel(decoded)
      }
    }
  }
}

make_impl!{i8}
make_impl!{i16}
make_impl!{i32}
make_impl!{i64}
make_impl!{i128}

#[cfg(test)]
mod tests {
  use super::*;
  use malachite::rational::Rational;
  use proptest::prelude::*;

  mod int_to_posit {
    use super::*;

    /// Aux function: check that `int` is converted to a posit with the correct rounding.
    fn is_correct_rounded<FromInt: crate::Int, const N: u32, const ES: u32, Int: crate::Int>(
      int: FromInt,
    ) -> bool
    where
      FromInt: Into<Rational> + RoundInto<Posit<N, ES, Int>>,
      Rational: TryFrom<Posit<N, ES, Int>, Error = super::rational::IsNaR>,
    {
      let posit: Posit<N, ES, Int> = int.round_into();
      if int == FromInt::MIN {
        posit == Posit::NAR
      } else {
        let exact: Rational = int.into();
        super::rational::is_correct_rounded(exact, posit)
      }
    }

    macro_rules! make_exhaustive {
      ($t:ident) => {
        mod $t {
          use super::*;

          #[test]
          fn posit_10_0_exhaustive() {
            for int in $t::MIN ..= $t::MAX {
              assert!(is_correct_rounded::<$t, 10, 0, i16>(int), "{:?}", int);
            }
          }

          #[test]
          fn posit_10_1_exhaustive() {
            for int in $t::MIN ..= $t::MAX {
              assert!(is_correct_rounded::<$t, 10, 1, i16>(int), "{:?}", int);
            }
          }

          #[test]
          fn posit_10_2_exhaustive() {
            for int in $t::MIN ..= $t::MAX {
              assert!(is_correct_rounded::<$t, 10, 2, i16>(int), "{:?}", int);
            }
          }

          #[test]
          fn posit_10_3_exhaustive() {
            for int in $t::MIN ..= $t::MAX {
              assert!(is_correct_rounded::<$t, 10, 3, i16>(int), "{:?}", int);
            }
          }

          #[test]
          fn posit_8_0_exhaustive() {
            for int in $t::MIN ..= $t::MAX {
              assert!(is_correct_rounded::<$t, 8, 0, i8>(int), "{:?}", int);
            }
          }

          #[test]
          fn p8_exhaustive() {
            for int in $t::MIN ..= $t::MAX {
              assert!(is_correct_rounded::<$t, 8, 2, i8>(int), "{:?}", int);
            }
          }

          #[test]
          fn p16_exhaustive() {
            for int in $t::MIN ..= $t::MAX {
              assert!(is_correct_rounded::<$t, 16, 2, i16>(int), "{:?}", int);
            }
          }

          #[test]
          fn p32_exhaustive() {
            for int in $t::MIN ..= $t::MAX {
              assert!(is_correct_rounded::<$t, 32, 2, i32>(int), "{:?}", int);
            }
          }

          #[test]
          fn p64_exhaustive() {
            for int in $t::MIN ..= $t::MAX {
              assert!(is_correct_rounded::<$t, 64, 2, i64>(int), "{:?}", int);
            }
          }
        }
      }
    }

    macro_rules! make_proptest {
      ($t:ident) => {
        mod $t {
          use super::*;

          proptest!{
            #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]

            #[test]
            fn posit_10_0_proptest(int in any::<$t>()) {
              assert!(is_correct_rounded::<$t, 10, 0, i16>(int), "{:?}", int);
            }

            #[test]
            fn posit_10_1_proptest(int in any::<$t>()) {
              assert!(is_correct_rounded::<$t, 10, 1, i16>(int), "{:?}", int);
            }

            #[test]
            fn posit_10_2_proptest(int in any::<$t>()) {
              assert!(is_correct_rounded::<$t, 10, 2, i16>(int), "{:?}", int);
            }

            #[test]
            fn posit_10_3_proptest(int in any::<$t>()) {
              assert!(is_correct_rounded::<$t, 10, 3, i16>(int), "{:?}", int);
            }

            #[test]
            fn posit_8_0_proptest(int in any::<$t>()) {
              assert!(is_correct_rounded::<$t, 8, 0, i8>(int), "{:?}", int);
            }

            #[test]
            fn p8_proptest(int in any::<$t>()) {
              assert!(is_correct_rounded::<$t, 8, 2, i8>(int), "{:?}", int);
            }

            #[test]
            fn p16_proptest(int in any::<$t>()) {
              assert!(is_correct_rounded::<$t, 16, 2, i16>(int), "{:?}", int);
            }

            #[test]
            fn p32_proptest(int in any::<$t>()) {
              assert!(is_correct_rounded::<$t, 32, 2, i32>(int), "{:?}", int);
            }

            #[test]
            fn p64_proptest(int in any::<$t>()) {
              assert!(is_correct_rounded::<$t, 64, 2, i64>(int), "{:?}", int);
            }
          }
        }
      }
    }

    make_exhaustive!{i8}
    make_exhaustive!{i16}
    make_proptest!{i32}
    make_proptest!{i64}
    make_proptest!{i128}
  }

  mod posit_to_int {
    use super::*;

    /// Aux function: check that `posit` rounds to `int`.
    fn is_correct_rounded<ToInt: crate::Int, const N: u32, const ES: u32, Int: crate::Int>(
      posit: Posit<N, ES, Int>,
      int: ToInt,
    ) -> bool
    where
      ToInt: RoundFrom<Posit<N, ES, Int>>,
      Rational: From<i32> + From<ToInt> + TryFrom<Posit<N, ES, Int>, Error = super::rational::IsNaR>,
      // TODO Why do I need the `From<i32>` bound hereeeeeee, rust pls fix
    {
      match Rational::try_from(posit) {
        Ok(exact) => {
          use malachite::base::num::arithmetic::traits::RoundToMultiple;
          use malachite::base::rounding_modes::RoundingMode;
          let rounded = exact.round_to_multiple(Rational::from(1), RoundingMode::Nearest).0;
          if rounded > Rational::from(ToInt::MAX) {
            int == ToInt::MIN
          } else if rounded < Rational::from(ToInt::MIN) {
            int == ToInt::MIN
          } else {
            Rational::from(int) == rounded
          }
        },
        Err(super::rational::IsNaR) => {
          int == ToInt::MIN
        }
      }
    }

    macro_rules! make_exhaustive {
      ($name:ident, $t:ty) => {
        mod $name {
          use super::*;

          #[test]
          fn i8_exhaustive() {
            for p in <$t>::cases_exhaustive_all() {
              let int: i8 = p.round_into();
              assert!(is_correct_rounded(p, int), "{p:?} {int}");
            }
          }

          #[test]
          fn i16_exhaustive() {
            for p in <$t>::cases_exhaustive_all() {
              let int: i16 = p.round_into();
              assert!(is_correct_rounded(p, int), "{p:?} {int}");
            }
          }

          #[test]
          fn i32_exhaustive() {
            for p in <$t>::cases_exhaustive_all() {
              let int: i32 = p.round_into();
              assert!(is_correct_rounded(p, int), "{p:?} {int}");
            }
          }

          #[test]
          fn i64_exhaustive() {
            for p in <$t>::cases_exhaustive_all() {
              let int: i64 = p.round_into();
              assert!(is_correct_rounded(p, int), "{p:?} {int}");
            }
          }

          #[test]
          fn i128_exhaustive() {
            for p in <$t>::cases_exhaustive_all() {
              let int: i128 = p.round_into();
              assert!(is_correct_rounded(p, int), "{p:?} {int}");
            }
          }
        }
      }
    }

    macro_rules! make_proptest {
      ($name:ident, $t:ty) => {
        mod $name {
          use super::*;

          proptest!{
            #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]

            #[test]
            fn i8_proptest(p in <$t>::cases_proptest_all()) {
              let int: i8 = p.round_into();
              assert!(is_correct_rounded(p, int), "{p:?} {int}");
            }

            #[test]
            fn i16_proptest(p in <$t>::cases_proptest_all()) {
              let int: i16 = p.round_into();
              assert!(is_correct_rounded(p, int), "{p:?} {int}");
            }

            #[test]
            fn i32_proptest(p in <$t>::cases_proptest_all()) {
              let int: i32 = p.round_into();
              assert!(is_correct_rounded(p, int), "{p:?} {int}");
            }

            #[test]
            fn i64_proptest(p in <$t>::cases_proptest_all()) {
              let int: i64 = p.round_into();
              assert!(is_correct_rounded(p, int), "{p:?} {int}");
            }

            #[test]
            fn i128_proptest(p in <$t>::cases_proptest_all()) {
              let int: i128 = p.round_into();
              assert!(is_correct_rounded(p, int), "{p:?} {int}");
            }
          }
        }
      }
    }

    make_exhaustive!{posit_10_0, Posit<10, 0, i16>}
    make_exhaustive!{posit_10_1, Posit<10, 1, i16>}
    make_exhaustive!{posit_10_2, Posit<10, 2, i16>}
    make_exhaustive!{posit_10_3, Posit<10, 3, i16>}
    make_exhaustive!{posit_8_0,  Posit<8,  0, i8 >}
    make_exhaustive!{p8, crate::p8}
    make_exhaustive!{p16, crate::p8}
    make_proptest!{p32, crate::p32}
    make_proptest!{p64, crate::p64}
  }
}
