use super::*;

macro_rules! impl_common {
  ($int:ty, $uint:ty) => {
    #[inline]
    fn to_be(self) -> Self { self.to_be() }

    #[inline]
    fn overflowing_add(self, other: Self) -> (Self, bool) { self.overflowing_add(other) }
  }
}

impl Unsigned for u8 {
  impl_common!{i8, u8}
}

impl Unsigned for u16 {
  impl_common!{i16, u16}
}

impl Unsigned for u32 {
  impl_common!{i32, u32}
}

impl Unsigned for u64 {
  impl_common!{i64, u64}
}

impl Unsigned for u128 {
  impl_common!{i128, u128}
}
