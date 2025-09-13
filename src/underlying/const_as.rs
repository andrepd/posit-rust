use super::*;

/// One line of the [`const_as`] function.
macro_rules! const_as_line {
  ($x:ident, $t:ty, $u:ty) => {
    if const { T::BITS == <$t>::BITS && U::BITS == <$u>::BITS } {
      // SAFETY: Because T, U, $t, $u, are guaranteed to be `iX`, then `$t` is `T` and `$u` is `U`;
      // therefore both transmute_copy are no-ops.
      let t = unsafe { ::core::mem::transmute_copy::<T, $t>(&$x) };
      let u = t as $u;
      return unsafe { ::core::mem::transmute_copy::<$u, U>(&u) }
    }
  }
}

/// A type-generic and `const` version of the keyword `as`, for casting between [`Int`]s.
///
/// ```ignore
/// # use fast_posit::underlying::const_as;
/// assert_eq!(const_as::<i16, i32>(1234i16), 1234i16 as i32);
/// assert_eq!(const_as::<i128, i64>(-16i128), -126i128 as i64);
/// ```
pub const fn const_as<T: Int, U: Int>(x: T) -> U {
  const_as_line!(x, i8, i8);
  const_as_line!(x, i8, i16);
  const_as_line!(x, i8, i32);
  const_as_line!(x, i8, i64);
  const_as_line!(x, i8, i128);
  const_as_line!(x, i16, i8);
  const_as_line!(x, i16, i16);
  const_as_line!(x, i16, i32);
  const_as_line!(x, i16, i64);
  const_as_line!(x, i16, i128);
  const_as_line!(x, i32, i8);
  const_as_line!(x, i32, i16);
  const_as_line!(x, i32, i32);
  const_as_line!(x, i32, i64);
  const_as_line!(x, i32, i128);
  const_as_line!(x, i64, i8);
  const_as_line!(x, i64, i16);
  const_as_line!(x, i64, i32);
  const_as_line!(x, i64, i64);
  const_as_line!(x, i64, i128);
  const_as_line!(x, i128, i8);
  const_as_line!(x, i128, i16);
  const_as_line!(x, i128, i32);
  const_as_line!(x, i128, i64);
  const_as_line!(x, i128, i128);
  unreachable!() // cannot be const { unreachable!() }
}

#[cfg(test)]
#[allow(overflowing_literals)]
mod tests {
  use super::*;

  #[test]
  fn test_1() {
    const VALUE: i32 = const_as(1i128);
    assert_eq!(VALUE, 1i32);
  }

  #[test]
  fn test_2() {
    const VALUE: i32 = const_as(-1i128);
    assert_eq!(VALUE, -1i32);
  }

  #[test]
  fn test_3() {
    const VALUE: i32 = const_as(0i128);
    assert_eq!(VALUE, 0i32);
  }

  #[test]
  fn test_4() {
    const VALUE: i32 = const_as(0xdeadbeef_i128);
    assert_eq!(VALUE, 0xdeadbeef_i32);
  }

  #[test]
  fn test_5() {
    const VALUE: i32 = const_as(0x71_i8);
    assert_eq!(VALUE, 0x00000071_i32);
  }

  #[test]
  fn test_6() {
    const VALUE: i32 = const_as(0xf1_i8);
    assert_eq!(VALUE, 0xfffffff1_i32);
  }

  #[test]
  fn test_7() {
    const VALUE: i16 = const_as(0x1337_i16);
    assert_eq!(VALUE, 0x1337_i16);
  }
}
