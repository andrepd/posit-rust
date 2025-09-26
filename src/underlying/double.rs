use super::{Double, Sealed};

macro_rules! impl_common {
  ($single:ty) => {
    type Single = $single;

    #[inline]
    fn components_hi_lo(self) -> ($single, $single) {
      let hi = (self >> <$single>::BITS) as $single;
      let lo = self as $single;
      (hi, lo)
    }

    #[inline]
    unsafe fn leading_run_minus_one(self) -> u32 {
      unsafe { <Self as Sealed>::leading_run_minus_one(self) }
    }
  };
}

impl Double for i16 {
  impl_common!{i8}
}

impl Double for i32 {
  impl_common!{i16}
}

impl Double for i64 {
  impl_common!{i32}
}

impl Double for i128 {
  impl_common!{i64}
}

/// There's no primitive type with double the precision of an `i128`. This is how we represent it.
#[derive(Debug)]
#[derive(Clone, Copy)]
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Pair<T> (T, T);

impl Double for Pair<i128> {
  type Single = i128;

  fn components_hi_lo(self) -> (i128, i128) {
    todo!()
  }

  unsafe fn leading_run_minus_one(self) -> u32 {
    todo!()
  }
}

impl core::ops::Shl<u32> for Pair<i128> {
  type Output = Self;

  fn shl(self, _rhs: u32) -> Self::Output {
    todo!()
  }
}

impl core::ops::Shr<u32> for Pair<i128> {
  type Output = Self;

  fn shr(self, _rhs: u32) -> Self::Output {
    todo!()
  }
}
