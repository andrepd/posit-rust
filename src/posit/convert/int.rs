use super::*;

use crate::underlying::const_as;

/// The kernel for converting a _signed_ int to a posit.
///
/// # Safety
///
/// `int` cannot be `FromInt::ZERO` or `FromInt::MIN`, or calling this function is *undefined
/// behaviour*.
#[inline]
unsafe fn round_from_signed_kernel<
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

/// The kernel for converting an _unsigned_ int to a posit (note it takes a signed int as
/// argument though).
///
/// # Safety
///
/// `int` cannot be `FromInt::ZERO` or `FromInt::MIN`, or calling this function is *undefined
/// behaviour*.
#[inline]
unsafe fn round_from_unsigned_kernel<
  FromInt: crate::Int,
  const N: u32,
  const ES: u32,
  Int: crate::Int,
>(int: FromInt) -> (Decoded<N, ES, Int>, Int) {
  let shift_right = if const { Int::BITS >= FromInt::BITS } {0} else {FromInt::BITS - Int::BITS};
  let shift_left = if const { Int::BITS <= FromInt::BITS } {0} else {Int::BITS - FromInt::BITS};

  // This function is almost entirely the same as [`round_from_signed_kernel`], only there are no
  // negative values: a leading 1 in `int` doesn't mean that the value is negative, it means that
  // it is positive, so the `frac` needs to be shifted 1 more place right in order to have a
  // leading 0.
  //
  // If this is the case, `overflow` will be 1, else 0.
  //
  // Example:
  //
  //   value: 0b10010011 (= 147)
  //    frac: 0b01001001 (1 = sticky)
  //     exp: +7 (= (8 - 2) frac width - 0 underflow + 1 overflow)
  //
  // SAFETY: `int` is not 0 nor MIN (function precondition)
  let leading_zeros = unsafe { int.leading_zeros_nonzero() };
  let overflow = u32::from(leading_zeros == 0);
  let underflow = leading_zeros.saturating_sub(1);
  let frac = (const_as::<FromInt, Int>(int << underflow >> shift_right) << shift_left).lshr(overflow);
  let exp = {
    let exp = Decoded::<N, ES, FromInt>::FRAC_WIDTH.wrapping_add(overflow).wrapping_sub(underflow);
    const_as::<i32, Int>(exp as i32)
  };
  let sticky = {
    let true_shift = shift_right.wrapping_add(overflow).saturating_sub(underflow);
    Int::from(int.mask_lsb(true_shift) != FromInt::ZERO)
  };

  (Decoded{frac, exp}, sticky)
}

macro_rules! make_impl {
  ($signed:ty, $unsigned:ty) => {
    impl<
      const N: u32,
      const ES: u32,
      Int: crate::Int,
    > RoundFrom<$signed> for Posit<N, ES, Int> {
      #[doc = concat!("Convert an `", stringify!($signed), "` into a `Posit`, [rounding according to the standard]:")]
      ///
      #[doc = concat!("  - If the value is [`", stringify!($signed), "::MIN`] (i.e. the value where the most significant bit is 1 and the rest are 0), it converts to [NaR](Posit::NAR).")]
      ///   - Otherwise, the integer value is rounded (if necessary).
      ///
      /// [rounding according to the standard]: https://posithub.org/docs/posit_standard-2.pdf#subsection.6.4
      fn round_from(value: $signed) -> Self {
        // Handle 0 and MIN. Remember that according to the standard, MIN (i.e. bit pattern
        // 0b1000…), is converted to NaR, and NaR is converted to MIN.
        if value == 0 { return Posit::ZERO }
        if value == <$signed>::MIN { return Posit::NAR }

        // This piece of code is only necessary in really extreme cases, like converting i128::MAX
        // to an 8-bit posit. But in those cases, we do need to guard against overflow on `exp`.
        if const { <$signed>::BITS as i128 > 1 << Decoded::<N, ES, Int>::FRAC_WIDTH } {
          let limit = 1 << (1 << Decoded::<N, ES, Int>::FRAC_WIDTH);
          if value >=  limit { return Posit::MAX }
          if value <= -limit { return Posit::MIN }
        }

        // SAFETY: `value` is not 0 or MIN
        let (result, sticky) = unsafe { round_from_signed_kernel(value) };
        // SAFETY: `frac` is not underflowing and `exp` cannot be greater than `FromInt::BITS`
        unsafe { result.encode_regular_round(sticky) }
      }
    }

    impl<
      const N: u32,
      const ES: u32,
      Int: crate::Int,
    > RoundFrom<$unsigned> for Posit<N, ES, Int> {
      #[doc = concat!("Convert an `", stringify!($unsigned), "` into a `Posit`, [rounding according to the standard]:")]
      ///
      ///   - If the value has the most significant bit set to 1 and the rest to 0, it converts to
      ///     [NaR](Posit::NAR).
      ///   - Otherwise, the integer value is rounded (if necessary).
      ///
      /// [rounding according to the standard]: https://posithub.org/docs/posit_standard-2.pdf#subsection.6.4
      fn round_from(value: $unsigned) -> Self {
        let int = value as $signed;

        // Handle 0 and MIN. Remember that according to the standard, MIN (i.e. bit pattern
        // 0b1000…), is converted to NaR, and NaR is converted to MIN.
        if int == 0 { return Posit::ZERO }
        if int == <$signed>::MIN { return Posit::NAR }

        // This piece of code is only necessary in really extreme cases, like converting u128::MAX
        // to an 8-bit posit. But in those cases, we do need to guard against overflow on `exp`.
        if const { <$unsigned>::BITS as i128 > 1 << Decoded::<N, ES, Int>::FRAC_WIDTH } {
          let limit = 1 << (1 << Decoded::<N, ES, Int>::FRAC_WIDTH);
          if value >= limit { return Posit::MAX }
        }

        // SAFETY: `value` is not 0 or MIN
        let (result, sticky) = unsafe { round_from_unsigned_kernel(value as $signed) };
        // SAFETY: `frac` is not underflowing and `exp` cannot be greater than `FromInt::BITS`
        unsafe { result.encode_regular_round(sticky) }
      }
    }
  }
}

make_impl!{i8, u8}
make_impl!{i16, u16}
make_impl!{i32, u32}
make_impl!{i64, u64}
make_impl!{i128, u128}

#[cfg(test)]
mod tests {
  use super::*;
  use malachite::rational::Rational;
  use proptest::prelude::*;

  /// Aux function: check that `int` is converted to a posit with the correct rounding.
  fn is_correct_rounded_i<FromInt: crate::Int, const N: u32, const ES: u32, Int: crate::Int>(
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

  /// Aux function: check that `uint` is converted to a posit with the correct rounding.
  fn is_correct_rounded_u<FromInt: crate::Int, const N: u32, const ES: u32, Int: crate::Int>(
    uint: FromInt::Unsigned,
  ) -> bool
  where
    FromInt::Unsigned: Into<Rational> + RoundInto<Posit<N, ES, Int>>,
    Rational: TryFrom<Posit<N, ES, Int>, Error = super::rational::IsNaR>,
  {
    let posit = uint.round_into();
    if FromInt::of_unsigned(uint) == FromInt::MIN {
      posit == Posit::NAR
    } else {
      let exact: Rational = uint.into();
      super::rational::is_correct_rounded(exact, posit)
    }
  }

  macro_rules! make_exhaustive {
    ($t:ident) => {
      mod $t {
        use super::*;
        use crate::underlying::Sealed;

        #[test]
        fn posit_10_0_exhaustive() {
          for int in $t::MIN ..= $t::MAX {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 10, 0, i16>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 10, 0, i16>(uint), "{:?}", uint);
          }
        }

        #[test]
        fn posit_10_1_exhaustive() {
          for int in $t::MIN ..= $t::MAX {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 10, 1, i16>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 10, 1, i16>(uint), "{:?}", uint);
          }
        }

        #[test]
        fn posit_10_2_exhaustive() {
          for int in $t::MIN ..= $t::MAX {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 10, 2, i16>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 10, 2, i16>(uint), "{:?}", uint);
          }
        }

        #[test]
        fn posit_10_3_exhaustive() {
          for int in $t::MIN ..= $t::MAX {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 10, 3, i16>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 10, 3, i16>(uint), "{:?}", uint);
          }
        }

        #[test]
        fn posit_8_0_exhaustive() {
          for int in $t::MIN ..= $t::MAX {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 8, 0, i8>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 8, 0, i8>(uint), "{:?}", uint);
          }
        }

        #[test]
        fn p8_exhaustive() {
          for int in $t::MIN ..= $t::MAX {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 8, 2, i8>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 8, 2, i8>(uint), "{:?}", uint);
          }
        }

        #[test]
        fn p16_exhaustive() {
          for int in $t::MIN ..= $t::MAX {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 16, 2, i16>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 16, 2, i16>(uint), "{:?}", uint);
          }
        }

        #[test]
        fn p32_exhaustive() {
          for int in $t::MIN ..= $t::MAX {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 32, 2, i32>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 32, 2, i32>(uint), "{:?}", uint);
          }
        }

        #[test]
        fn p64_exhaustive() {
          for int in $t::MIN ..= $t::MAX {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 64, 2, i64>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 64, 2, i64>(uint), "{:?}", uint);
          }
        }
      }
    }
  }

  macro_rules! make_proptest {
    ($t:ident) => {
      mod $t {
        use super::*;
        use crate::underlying::Sealed;

        proptest!{
          #![proptest_config(ProptestConfig::with_cases(crate::PROPTEST_CASES))]

          #[test]
          fn posit_10_0_proptest(int in any::<$t>()) {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 10, 0, i16>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 10, 0, i16>(uint), "{:?}", uint);
          }

          #[test]
          fn posit_10_1_proptest(int in any::<$t>()) {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 10, 1, i16>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 10, 1, i16>(uint), "{:?}", uint);
          }

          #[test]
          fn posit_10_2_proptest(int in any::<$t>()) {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 10, 2, i16>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 10, 2, i16>(uint), "{:?}", uint);
          }

          #[test]
          fn posit_10_3_proptest(int in any::<$t>()) {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 10, 3, i16>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 10, 3, i16>(uint), "{:?}", uint);
          }

          #[test]
          fn posit_8_0_proptest(int in any::<$t>()) {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 8, 0, i8>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 8, 0, i8>(uint), "{:?}", uint);
          }

          #[test]
          fn p8_proptest(int in any::<$t>()) {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 8, 2, i8>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 8, 2, i8>(uint), "{:?}", uint);
          }

          #[test]
          fn p16_proptest(int in any::<$t>()) {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 16, 2, i16>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 16, 2, i16>(uint), "{:?}", uint);
          }

          #[test]
          fn p32_proptest(int in any::<$t>()) {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 32, 2, i32>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 32, 2, i32>(uint), "{:?}", uint);
          }

          #[test]
          fn p64_proptest(int in any::<$t>()) {
            let uint = int.as_unsigned();
            assert!(is_correct_rounded_i::<$t, 64, 2, i64>(int), "{:?}", int);
            assert!(is_correct_rounded_u::<$t, 64, 2, i64>(uint), "{:?}", uint);
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