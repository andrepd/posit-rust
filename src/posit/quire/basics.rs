use super::*;

impl<
  const N: u32,
  const ES: u32,
  const SIZE: usize,
> Quire<N, ES, SIZE> {
  /// Construct a quire from its raw bit representation, in big endian order.
  pub const fn from_bits(bytes: [u8; SIZE]) -> Self {
    Self(bytes)
  }

  /// Access the storage as an array of `u64`s. 
  #[inline]
  pub(crate) const fn as_u64_array(&self) -> &[u64] {
    let ptr = self.0.as_ptr() as *const u64;
    let len = SIZE / 8;
    // SAFETY: ptr and len form a valid slice; the size and alignment is correct, and any bit
    // pattern is a valid u64 value.
    unsafe { core::slice::from_raw_parts(ptr, len) }
  }

  /// Auxiliary const: the maximum (positive) exponent of a `Posit<N, ES, Int>`. The size of the
  /// quire is directly related to this (see [`Self::MIN_SIZE`] and [`Self::WIDTH`] below).
  const MAX_EXP: u32 = {
    assert!(ES < 20, "Cannot use the quire with very high ES (≥ 20)");
    let max_regime = N - 2;
    max_regime << ES
  };

  /// The minimum size of a quire for `Posit<N, ES, Int>`.
  pub const MIN_SIZE: usize = {
    // At worst, need to be able to represent [Posit::MAX]² + [Posit::MIN]² as a fixed point
    // number. So that's a number of bits equal to 2×2×max_exp. Then add 1 sign bit: that's the
    // minimum quire size in bits.
    let min_size_bits = 4 * Self::MAX_EXP + 1;
    min_size_bits.div_ceil(8) as usize
  };

  /// The minimum number of operations on the quire that can lead to overflow is 
  /// 2 <sup>[`PROD_LIMIT`](Self::PROD_LIMIT)</sup>; any number of [Self::add_prod] calls smaller
  /// than that is guaranteed not to overflow.
  pub const PROD_LIMIT: u32 = {
    // The biggest possible product (Posit::MAX * Posit::MAX) takes `4 * MAX_EXP` bits. It can be
    // accumulated `2 ^ M` times, where `M` is the difference between that and this quire's
    // `SIZE`, before it overflows.
    let min_size_bits = 4 * Self::MAX_EXP + 1;
    8 * SIZE as u32 - min_size_bits
  };

  /// The minimum number of additions of posits that can lead to overflow is 
  /// 2 <sup>[`SUM_LIMIT`](Self::SUM_LIMIT)</sup>; any number of `+=` or `-=` operations smaller
  /// than that is guaranteed not to overflow.
  pub const SUM_LIMIT: u32 = {
    // The biggest possible posit value (Posit::MAX) takes `3 * MAX_EXP` bits. It can be
    // accumulated `2 ^ M` times, where `M` is the difference between that and this quire's
    // `SIZE`, before it overflows.
    let min_size_bits = 3 * Self::MAX_EXP + 1;
    8 * SIZE as u32 - min_size_bits
  };

  /// The position of the fixed point, that is: "1.0" is represented in the quire as `1 << WIDTH`.
  const WIDTH: u32 = {
    assert!(SIZE >= Self::MIN_SIZE, "The quire type has fewer than the minimum number of bytes");
    2 * Self::MAX_EXP
  };

  // TODO assert this on operations with posits (cannot assert here because needs to take into
  // account the posit's underlying Int): 
  // assert!(SIZE % N == 0, "The size of the quire type is not a multiple of the posit size");

  /// A quire that represents the posit number 0.
  pub const ZERO: Self = Self([0; SIZE]);

  /// A quire that represents the posit value `NaR`.
  pub const NAR: Self = {
    assert!(SIZE % 8 == 0, "Quire SIZE must be a multiple of 64 bits (8 bytes)");
    let mut nar = Self::ZERO;
    nar.0[0] = u8::MIN;
    nar
  };

  /// Checks whether `self` represents a NaR value.
  pub const fn is_nar(&self) -> bool {
    // This is more optimised than it looks. If the quire is not NaR, which is the "normal" and
    // thus more important case to optimise, then most likely it will either start with
    // `0b00…001…` (positive) of `0b11…110…` (negative), and thus return right away on the first
    // if statement. This is because the only way it starts with `0b1000…` and yet is not NaR is
    // if it's very very close to overflowing on the negative side; this is *exceedingly*
    // unlikely.
    //
    // Therefore, for almost all cases where the quire is not NaR, we only need a compare and
    // branch. Only on when the quire is NaR, or in the rare cases where it's not NaR but still
    // starts with `0b1000…`, will we need to scan through the whole thing.
    let quire = self.as_u64_array();
    if quire[0] != (i64::MIN as u64).to_be() { return false }  // TODO mark likely?
    // Written in this awkward way because it's a `const fn`...
    let mut i = 1;
    while i < quire.len() {
      if quire[i] != 0 { return false }
      i += 1
    }
    true
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  /// Source: <https://posithub.org/docs/posit_standard-2.pdf#subsection.3.4>
  #[test]
  fn width() {
    assert_eq!(Quire::<8,  2, {2 * 8 }>::WIDTH, 8 * 8  - 16);
    assert_eq!(Quire::<16, 2, {2 * 16}>::WIDTH, 8 * 16 - 16);
    assert_eq!(Quire::<32, 2, {2 * 32}>::WIDTH, 8 * 32 - 16);
    assert_eq!(Quire::<64, 2, {2 * 64}>::WIDTH, 8 * 64 - 16);
  }

  /// Source: <https://posithub.org/docs/posit_standard-2.pdf#subsection.3.2>
  #[test]
  fn min_size() {
    assert_eq!(8 * Quire::<8,  2, {2 * 8 }>::MIN_SIZE, 96  + 8);
    assert_eq!(8 * Quire::<16, 2, {2 * 16}>::MIN_SIZE, 224 + 8);
    assert_eq!(8 * Quire::<32, 2, {2 * 32}>::MIN_SIZE, 480 + 8);
    assert_eq!(8 * Quire::<64, 2, {2 * 64}>::MIN_SIZE, 992 + 8);
  }

  /// Source: <https://posithub.org/docs/posit_standard-2.pdf#subsection.3.2>
  #[test]
  fn sum_limit() {
    assert_eq!(Quire::<8,  2, {2 * 8 }>::SUM_LIMIT, 55);
    assert_eq!(Quire::<16, 2, {2 * 16}>::SUM_LIMIT, 87);
    assert_eq!(Quire::<32, 2, {2 * 32}>::SUM_LIMIT, 151);
    assert_eq!(Quire::<64, 2, {2 * 64}>::SUM_LIMIT, 279);
  }

  /// Source: <https://posithub.org/docs/posit_standard-2.pdf#subsection.3.2>
  #[test]
  fn prod_limit() {
    assert_eq!(Quire::<8,  2, {2 * 8 }>::PROD_LIMIT, 31);
    assert_eq!(Quire::<16, 2, {2 * 16}>::PROD_LIMIT, 31);
    assert_eq!(Quire::<32, 2, {2 * 32}>::PROD_LIMIT, 31);
    assert_eq!(Quire::<64, 2, {2 * 64}>::PROD_LIMIT, 31);
  }

  #[test]
  fn is_nar() {
    type q8 = Quire<8, 2, {2 * 8}>;
    let bits = [0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    assert!(q8::from_bits(bits).is_nar());
    let bits = [0x81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    assert!(!q8::from_bits(bits).is_nar());
    let bits = [0x80, 0, 0x42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    assert!(!q8::from_bits(bits).is_nar());
    let bits = [0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x42, 0, 0, 0];
    assert!(!q8::from_bits(bits).is_nar());
    let bits = [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff];
    assert!(!q8::from_bits(bits).is_nar());
    let bits = [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff];
    assert!(!q8::from_bits(bits).is_nar());
  }
}
