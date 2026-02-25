use super::*;

impl<
  const N: u32,
  const ES: u32,
  const SIZE: usize,
> Quire<N, ES, SIZE> {
  /// The quire size in bits.
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(q16::BITS, 256);
  /// ```
  pub const BITS: u32 = Self::SIZE as u32 * 8;

  /// The quire size in bytes.
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(q16::SIZE, 32);
  /// ```
  pub const SIZE: usize = {
    assert!(SIZE >= Self::MIN_SIZE, "This quire type has fewer than the minimum number of bytes");
    // if const { SIZE < Self::MIN_SIZE } { compile_error!("asdf") }
    SIZE
  };

  /// Construct a quire from its raw bit representation, as a byte array in little-endian order.
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// let quire = q8::from_le_bytes([0,0,0,0,0,0, 1,0,0,0,0,0, 0,0,0,0]);
  /// assert_eq!(p8::round_from(&quire), p8::ONE);
  /// ```
  pub const fn from_le_bytes(bytes: [u8; SIZE]) -> Self {
    Self(bytes)
  }

  /// Construct a quire from its raw bit representation, as a byte array in big-endian order.
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// let quire = q8::from_be_bytes([0,0,0,0, 0,0,0,0,0,1, 0,0,0,0,0,0]);
  /// assert_eq!(p8::round_from(&quire), p8::ONE);
  /// ```
  pub const fn from_be_bytes(mut bytes: [u8; SIZE]) -> Self {
    bytes.as_mut_slice().reverse();
    Self::from_le_bytes(bytes)
  }

  /// The quire size in u64s (= [`BITS`](Self::BITS) / 64).
  pub(crate) const LEN_U64: usize = Self::BITS as usize / 64;

  /// Access the storage as an array of `u64`s, in little endian order.
  ///
  /// Limitation: even though the return size is known, we cannot return an `&[u64; N]` due to
  /// limitations in the Rust type system. We have to hope that the compiler will inline and fold
  /// the slice len :)
  #[inline(always)]
  pub(crate) const fn as_u64_array(&self) -> &[u64] {
    const { assert!(SIZE % 8 == 0, "Quire SIZE must be a multiple of 64 bits (8 bytes)"); }
    const { assert!(cfg!(target_endian = "little"), "Big-endian targets are not currently supported") }
    let ptr = self.0.as_ptr() as *const u64;
    // SAFETY: ptr and len form a valid slice; the size and alignment is correct, and any bit
    // pattern is a valid u64 value.
    unsafe { core::slice::from_raw_parts(ptr, Self::LEN_U64) }
  }

  #[inline(always)]
  pub(crate) const fn as_u64_array_mut(&mut self) -> &mut [u64] {
    const { assert!(SIZE % 8 == 0, "Quire SIZE must be a multiple of 64 bits (8 bytes)"); }
    const { assert!(cfg!(target_endian = "little"), "Big-endian targets are not currently supported") }
    let ptr = self.0.as_mut_ptr() as *mut u64;
    // SAFETY: ptr and len form a valid slice; the size and alignment is correct, and any bit
    // pattern is a valid u64 value.
    unsafe { core::slice::from_raw_parts_mut(ptr, Self::LEN_U64) }
  }

  #[inline(always)]
  pub(crate) const fn as_int_array<Int: crate::Int>(&self) -> &[Int] {
    const { assert!(Self::BITS % Int::BITS == 0, "Quire BITS must be a multiple of Int bits"); }
    const { assert!(cfg!(target_endian = "little"), "Big-endian targets are not currently supported") }
    let ptr = self.0.as_ptr() as *const Int;
    // SAFETY: ptr and len form a valid slice; the size and alignment is correct, and any bit
    // pattern is a valid Int value.
    unsafe { core::slice::from_raw_parts(ptr, Self::BITS as usize / Int::BITS as usize) }
  }

  /// Auxiliary const: the maximum (positive) exponent of a `Posit<N, ES, Int>`. The size of the
  /// quire is directly related to this (see [`Self::MIN_SIZE`] and [`Self::WIDTH`] below).
  const MAX_EXP: u32 = {
    assert!(ES < 20, "Cannot use the quire with very high ES (≥ 20)");
    let max_regime = N - 2;
    max_regime << ES
  };

  /// The minimum [`SIZE`](Self::SIZE) of a quire for `Posit<N, ES, Int>`, in bytes.
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(q16::MIN_SIZE, 29);
  /// ```
  pub const MIN_SIZE: usize = {
    // At worst, need to be able to represent [Posit::MAX]² + [Posit::MIN]² as a fixed point
    // number. So that's a number of bits equal to 2×2×max_exp. Then add 1 sign bit: that's the
    // minimum quire size in bits.
    let min_size_bits = 4 * Self::MAX_EXP + 1;
    min_size_bits.div_ceil(8) as usize
  };

  /// The minimum number of operations on the quire that can lead to overflow is
  /// 2 <sup>[`PROD_LIMIT`](Self::PROD_LIMIT)</sup>; any number of [`Self::add_prod`] calls
  /// smaller than that is guaranteed not to overflow.
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(q32::PROD_LIMIT, 31);  // Can do at least 2^31 - 1 products without overflow
  /// ```
  pub const PROD_LIMIT: u32 = {
    // The biggest possible product (Posit::MAX * Posit::MAX) takes `4 * MAX_EXP` bits. It can be
    // accumulated `2 ^ M` times, where `M` is the difference between that and this quire's
    // `SIZE`, before it overflows.
    let min_size_bits = 4 * Self::MAX_EXP + 1;
    Self::BITS as u32 - min_size_bits
  };

  /// The minimum number of additions of posits that can lead to overflow is
  /// 2 <sup>[`SUM_LIMIT`](Self::SUM_LIMIT)</sup>; any number of `+=` or `-=` operations smaller
  /// than that is guaranteed not to overflow.
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert_eq!(q32::SUM_LIMIT, 151);  // Can sum at least 2^151 - 1 terms without overflow
  /// ```
  pub const SUM_LIMIT: u32 = {
    // The biggest possible posit value (Posit::MAX) takes `3 * MAX_EXP` bits. It can be
    // accumulated `2 ^ M` times, where `M` is the difference between that and this quire's
    // `SIZE`, before it overflows.
    let min_size_bits = 3 * Self::MAX_EXP + 1;
    Self::BITS as u32 - min_size_bits
  };

  /// The position of the fixed point, that is: "1.0" is represented in the quire as `1 << WIDTH`.
  pub(crate) const WIDTH: u32 = {
    let _ = Self::SIZE;
    2 * Self::MAX_EXP
  };

  // TODO assert this on operations with posits (cannot assert here because needs to take into
  // account the posit's underlying Int):
  // assert!(SIZE % N == 0, "The size of the quire type is not a multiple of the posit size");

  /// A quire that represents the posit number 0.
  pub const ZERO: Self = Self([0; SIZE]);

  /// A quire that represents the posit value `NaR`.
  pub const NAR: Self = {
    let mut nar = Self::ZERO;
    nar.0[Self::SIZE - 1] = i8::MIN as u8;
    nar
  };

  /// Checks whether `self` represents a NaR value.
  ///
  /// # Example
  ///
  /// ```
  /// # use fast_posit::*;
  /// assert!(q32::NAR.is_nar());
  /// ```
  pub const fn is_nar(&self) -> bool {
    let _ = Self::NAR;
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
    let quire: &[u64] = self.as_u64_array();
    if quire[quire.len() - 1] != i64::MIN as u64 { return false }  // TODO mark likely?
    // Written in this awkward way because it's a `const fn`...
    let mut i = 0;
    while i < quire.len() - 1 {
      if quire[i] != 0 { return false }
      i += 1
    }
    true
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  /// Source: <https://posithub.org/docs/posit_standard-2.pdf#subsection.3.2>
  #[test]
  fn bits() {
    assert_eq!(crate::q8::BITS, 128);
    assert_eq!(crate::q16::BITS, 256);
    assert_eq!(crate::q32::BITS, 512);
    assert_eq!(crate::q64::BITS, 1024);
  }

  /// Source: <https://posithub.org/docs/posit_standard-2.pdf#subsection.3.2>
  #[test]
  fn size() {
    assert_eq!(crate::q8::SIZE, 16);
    assert_eq!(crate::q16::SIZE, 32);
    assert_eq!(crate::q32::SIZE, 64);
    assert_eq!(crate::q64::SIZE, 128);
  }

  /// Source: <https://posithub.org/docs/posit_standard-2.pdf#subsection.3.4>
  #[test]
  fn width() {
    assert_eq!(crate::q8::WIDTH, 8 * 8  - 16);
    assert_eq!(crate::q16::WIDTH, 8 * 16 - 16);
    assert_eq!(crate::q32::WIDTH, 8 * 32 - 16);
    assert_eq!(crate::q64::WIDTH, 8 * 64 - 16);
  }

  /// Source: <https://posithub.org/docs/posit_standard-2.pdf#subsection.3.2>
  #[test]
  fn min_size() {
    assert_eq!(8 * crate::q8::MIN_SIZE, 96  + 8);
    assert_eq!(8 * crate::q16::MIN_SIZE, 224 + 8);
    assert_eq!(8 * crate::q32::MIN_SIZE, 480 + 8);
    assert_eq!(8 * crate::q64::MIN_SIZE, 992 + 8);
  }

  /// With the above `MIN_SIZE`s, still compiles fine, but below that it doesn't (see
  /// [tests_compile_fail]).
  #[test]
  fn min_size_compiles() {
    let _ = Quire::<8,  2, {96 /8 + 1}>::SIZE;
    let _ = Quire::<16, 2, {224/8 + 1}>::SIZE;
    let _ = Quire::<32, 2, {480/8 + 1}>::SIZE;
    let _ = Quire::<64, 2, {992/8 + 1}>::SIZE;
  }

  /// Source: <https://posithub.org/docs/posit_standard-2.pdf#subsection.3.2>
  #[test]
  fn sum_limit() {
    assert_eq!(crate::q8::SUM_LIMIT, 55);
    assert_eq!(crate::q16::SUM_LIMIT, 87);
    assert_eq!(crate::q32::SUM_LIMIT, 151);
    assert_eq!(crate::q64::SUM_LIMIT, 279);
  }

  /// Source: <https://posithub.org/docs/posit_standard-2.pdf#subsection.3.2>
  #[test]
  fn prod_limit() {
    assert_eq!(crate::q8::PROD_LIMIT, 31);
    assert_eq!(crate::q16::PROD_LIMIT, 31);
    assert_eq!(crate::q32::PROD_LIMIT, 31);
    assert_eq!(crate::q64::PROD_LIMIT, 31);
  }

  #[test]
  fn is_nar() {
    assert!(crate::q8::NAR.is_nar());
    assert!(crate::q16::NAR.is_nar());
    assert!(crate::q32::NAR.is_nar());
    assert!(crate::q64::NAR.is_nar());
  }

  #[test]
  fn is_nar_manual() {
    let bits = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x80];
    assert!(crate::q8::from_le_bytes(bits).is_nar());
    let bits = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x81];
    assert!(!crate::q8::from_le_bytes(bits).is_nar());
    let bits = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x42, 0, 0x80];
    assert!(!crate::q8::from_le_bytes(bits).is_nar());
    let bits = [0, 0, 0, 0x42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x80];
    assert!(!crate::q8::from_le_bytes(bits).is_nar());
    let bits = [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f];
    assert!(!crate::q8::from_le_bytes(bits).is_nar());
    let bits = [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff];
    assert!(!crate::q8::from_le_bytes(bits).is_nar());
  }
}

mod tests_compile_fail {
  // TODO fix sizes in the future when relaxing the "multiple of 64 bits" constraint

  /// ```compile_fail
  /// use fast_posit::Quire;
  /// let mut q: Quire<8, 2, /*12*/ 8> = Quire::ZERO;
  /// q += fast_posit::p8::ONE;
  /// ```
  #[allow(dead_code)]
  fn quire_size_too_small_8() {}

  /// ```compile_fail
  /// use fast_posit::Quire;
  /// let mut q: Quire<16, 2, /*28*/ 24> = Quire::ZERO;
  /// q += fast_posit::p16::ONE;
  /// ```
  #[allow(dead_code)]
  fn quire_size_too_small_16() {}

  /// ```compile_fail
  /// use fast_posit::Quire;
  /// let mut q: Quire<32, 2, /*60*/ 56> = Quire::ZERO;
  /// q += fast_posit::p32::ONE;
  /// ```
  #[allow(dead_code)]
  fn quire_size_too_small_32() {}

  /// ```compile_fail
  /// use fast_posit::Quire;
  /// let mut q: Quire<64, 2, /*124*/ 120> = Quire::ZERO;
  /// q += fast_posit::p64::ONE;
  /// ```
  #[allow(dead_code)]
  fn quire_size_too_small_64() {}
}
