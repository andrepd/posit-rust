use super::*;

macro_rules! impl_common {
  ($int:ty, $uint:ty) => {
    #[inline]
    fn to_be(self) -> Self { self.to_be() }

    #[inline]
    fn overflowing_add(self, other: Self) -> (Self, bool) { self.overflowing_add(other) }
  }
}

macro_rules! impl_common_doubling {
  ($int:ty, $uint:ty, $udouble:ty) => {
    #[inline]
    fn shift_sqrt(self, precision: u32) -> (Self, bool) {
      let double = self as $udouble << precision;
      let result = double.isqrt();
      debug_assert!(<$uint>::try_from(result).is_ok());
      let inexact = result * result != double;
      (result as $uint, inexact)
    }
  }
}

impl Unsigned for u8 {
  impl_common!{i8, u8}
  impl_common_doubling!{i8, u8, u16}
}

impl Unsigned for u16 {
  impl_common!{i16, u16}
  impl_common_doubling!{i16, u16, u32}
}

impl Unsigned for u32 {
  impl_common!{i32, u32}
  impl_common_doubling!{i32, u32, u64}
}

impl Unsigned for u64 {
  impl_common!{i64, u64}
  impl_common_doubling!{i64, u64, u128}
}

impl Unsigned for u128 {
  impl_common!{i128, u128}
  
  fn shift_sqrt(self, _precision: u32) -> (Self, bool) {
    todo!()
  }
}
