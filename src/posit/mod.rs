//! This module and its submodules contain a software implementation of a standard-compliant Posit
//! floating point type, with arbitrary width and exponent width (up to 128).
//!
//! This module is **EXTENSIVELY** documented! If you want to learn more about Posits and an
//! optimised software implementation thereof (or about floating point implementations in
//! general!), you might profit from reading carefully through the code :) We assume basic
//! familiarity with both the Posit format and with two's complement integer arithmetic;
//! everything else we try to explain.
//!
//! If you know nothing about Posits and want to learn more, a good place to start is
//! <https://posithub.org/docs/Posits4.pdf>. The most up to date standard is at
//! <https://posithub.org/docs/posit_standard-2.pdf>.
//!
//! Some notation used in the comments:
//!
//!   - **Leftmost bits/msb**: most-significant bits.
//!   - **Rightmost bits/lsb**: least-significant bits.
//!   - **Bit 0, bit 1, .. bit N-1**: numbered least significant to most significant.
//!   - [a; b[ for a range that is closed (inclusive) on `a` and open (exclusive) on `b`.
//!
//! Suggested reading order: [Posit] and [Decoded] types, [basics] and [constants](consts),
//! [decode] implementation (Posit→Decoded), [encode] implementation (Decoded→Posit),
//! [elementary arithmetic](ops).
//!
//! # Testing
//!
//! Extensive tests are included. When possible, we check all inputs exhaustively (e.g.: adding two
//! 8-bit posits, there are only 256² possible inputs). Whenever this is not feasible (e.g: adding
//! two 64-bit posits), we make use of the `proptest` crate, which allows us to probabilistically
//! test inputs from a random distribution.
//!
//! Another key ingredient in the testing process is in the `rational` submodule. There, we define
//! some tools to convert to and from *arbitrary precision* rational numbers. Since any non-NaR
//! posit is a rational number, we can test any function in this crate involving posits by simply
//! checking that the output matches the output of the equivalent function using
//! infinite-precision rationals. For instance: to test addition of two posits, we simply check
//! that `rational(a) + rational(b) == rational(a + b)`, i.e. adding the posits yields the same
//! result as adding the arbitrary-precision rationals (modulo rounding, of course).

/// A *posit* floating point number with `N` bits and `ES` exponent bits, using `Int` as its
/// underlying type.
///
/// If `Int` = `iX`, then `N` must be in the range `3 ..= X`, and `ES` must be in the range `0 ..
/// N`. If this is not the case, a **compile-time** error will be raised.
///
/// Type aliases are provided at the [crate root](crate#types) for the posit types defined in
/// [the standard](https://posithub.org/docs/posit_standard-2.pdf#subsection.3.1).
///
/// # Example
///
/// ```
/// # use fast_posit::Posit;
/// // A 32-bit posit with 2-bit exponent field, represented in a 32-bit machine type.
/// type Foo = Posit<32, 2, i32>;
/// // A 6-bit posit with 1-bit exponent field, represented in an 8-bit machine type.
/// type Bar = Posit<6, 1, i8>;
/// ```
///
/// The standard [`p8`](crate::p8), [`p16`](crate::p16), [`p32`](crate::p32), and
/// [`p64`](crate::p64) types are simply type aliases for `Posit<X, 2, iX>`.
///
/// Note that `Posit` will have the same size (and alignment) as its `Int` parameter, so it's
/// currently not possible to create e.g. a 4-bit posit that only takes 4 bits in memory.
///
/// If the combination of parameters is invalid, the code will not compile.
///
/// ```compile_fail
/// # use fast_posit::Posit;
/// type Foo = Posit<40, 2, i32>;   // N=40 too large for i32
/// # let _ = Foo::ONE;
/// ```
/// ```compile_fail
/// # use fast_posit::Posit;
/// type Bar = Posit<1, 0, i8>;     // N=1 can't be ≤ 2
/// # let _ = Bar::ONE;
/// ```
/// ```compile_fail
/// # use fast_posit::Posit;
/// type Baz = Posit<32, 33, i32>;  // ES=33 too big for N=32
/// # let _ = Baz::ONE + Baz::ONE;
/// ```
pub struct Posit<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> (Int);

/// In order to perform most nontrivial operations, a `Posit<N, ES, Int>` needs to be *decoded*
/// into the form `f × 2^e` (with rational fraction `f` and integer exponent `e`), a form that is
/// amenable for further manipulation.
///
/// This is represented as a `Decoded<N, ES, Int>`, a struct that contains two integer fields,
/// `frac` and `exp`, such that it represents the value
///
/// ```text
/// (frac / FRAC_DENOM) × (2 ^ exp)
/// ```
///
/// where `FRAC_DENOM` is a fixed power of two, equal to `2 ^ (B-2)`, where `B` = `Int::BITS`.
///
/// That is to say: this encodes the `f × 2^e` referred above using two integers:
/// - The integer [`exp`](Self::exp) is the integer `e`, and
/// - The integer [`frac`](Self::frac) is the rational `f` *with an implicit denominator* of
///   `1 << (B-2)`.
///
/// Another way to think of it is that `frac` is a fixed-point rational number, where the dot is
/// two places from the left. For instance (for an 8-bit `frac`):
///
///   - `0b01_000000` = +1.00
///   - `0b01_100000` = +1.50
///   - `0b10_000000` = -2.00
///   - `0b11_100000` = -0.50
///
/// and so on.
///
/// The docstrings for [both](Decoded::frac) [fields](Decoded::exp) contain more detail, more
/// examples, and further considerations about their values.
///
/// Extracting these fields from a posit, and converting back to a posit with correct rounding, can
/// be done **very** efficiently, and indeed those two algorithms lie at the heart of many
/// operations: [`Posit::decode_regular`] and [`Decoded::encode_regular_round`].
#[derive(Clone, Copy)]
#[derive(Eq, PartialEq, Hash)]
pub struct Decoded<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> {
  /// The `frac`tion is the `frac / FRAC_DENOM` part of the posit value. Since the constant
  /// `FRAC_DENOM` = `1 << (Int::BITS - 2)` is fixed, one can simply look at the values of `frac`
  /// as fixed-point numbers where the dot is two places from the left.
  ///
  /// Examples (8-bit posit):
  ///
  ///   - `0b01_000000`  = +1.0
  ///   - `0b01_100000`  = +1.5
  ///   - `0b01_110000`  = +1.75
  ///   - `0b01_010000`  = +1.25
  ///   - `0b01_111111`  = +1.984375
  ///
  /// and negative numbers
  ///
  ///   - `0b10_000000`  = -2.0
  ///   - `0b10_100000`  = -1.5
  ///   - `0b10_110000`  = -1.25
  ///   - `0b10_010000`  = -1.75
  ///   - `0b10_000001`  = -1.984375
  ///   - `0b10_111111`  = -1.015625
  ///
  /// # Valid ranges
  ///
  /// Now, the result of [`Posit::decode_regular`] always has a `frac` lying within the following
  /// ranges:
  ///
  ///   - [+1.0, +2.0[ for positive numbers
  ///   - [-2.0, -1.0[ for negative numbers
  ///
  /// Note that these are not symmetric! In particular, a positive `frac` may be +1.0
  /// (`0b01_000…`) but not +2.0, and a negative `frac` may be -2.0 (`0b10_000…`) but not -1.0.
  /// This is an artefact of how the posit format works, and it enables very efficient
  /// implementations at key points in many algorithms.
  ///
  /// In terms of bit patterns, this corresponds to requiring that the `frac` starts with either
  /// `0b01` (positive) or `0b10` (negative), and never with `0b00` or `0b11`.
  ///
  /// Likewise, for the input to [`Decoded::encode_regular`] we **also** require that
  /// `frac` **must** always be in such a valid range. Whenever this is not the case, we say that
  /// the `frac` is "*underflowing*". This is checked, together with the bounds for
  /// [`exp`](Self::exp), by the function [`Self::is_normalised`].
  ///
  /// This is important. Often, when we feed a [`Decoded`] to [`Decoded::encode_regular`], such as
  /// when implementing arithmetic operations, we will need to for instance adjust the `frac` so
  /// that it is in the correct range, and possibly compensate by adjusting the `exp`onent in the
  /// opposite direction.
  pub frac: Int,
  /// The `exp`onent is the `2 ^ exp` part of the posit value.
  ///
  /// The `exp` field is made up from both the "regime" and "exponent" fields of a posit: the
  /// lowest `ES` bits are the exponent field verbatim, while the highest come from the regime's
  /// length and sign. The structure is apparent when looking at the `exp` in binary.
  ///
  /// Examples (8-bit posit, 2-bit exponent):
  ///
  ///   - `0b00001_01` (exp = +5, regime = +1, exponent = +1)
  ///   - `0b11110_11` (exp = -5, regime = -2, exponent = +3)
  ///
  /// # Valid ranges
  ///
  /// For reasons that become apparent when implementing [`Decoded::encode_regular`], we will also
  /// require that `exp >> ES` lies in a certain range, namely between `Int::MIN / 2` and
  /// `Int::MAX / 2`, inclusive.
  ///
  /// In terms of bit patterns, this corresponds to requiring that `exp >> ES` starts with `0b00`
  /// (positive) or `0b11` (negative), and never with `0b01` or `0b10`. Plainly, this is only an
  /// issue if `ES` is 0, or the bounds automatically hold.
  ///
  /// It may happen that, for posits of very high dynamic range, the maximum exponent would
  /// overflow an `Int`, and thus not be able to be stored in the `exp` field. Although his is not
  /// a concern unless `ES` takes absurdly big values, in that case compile-time checks will
  /// trigger an error, and suggest the user lower the dynamic range or pick a bigger `Int`.
  pub exp: Int,
}

/// Some basic constants and functions, such as a check that `N` and `ES` make sense for `Int`, or
/// functions to convert to/from raw bits.
mod basics;

/// Manual implementation of `derive`able traits for [`Posit`]. This is because the derive macro
/// isn't smart enough to figure some transitive bounds in `Int` → `Sealed`, so we would be left
/// with superfluous bounds on those traits.
mod traits;

/// Numeric constants: zero, NaR, min, min_positive, etc.
mod consts;

/// [`Posit`] → [`Decoded`].
mod decode;

/// [`Decoded`] → [`Posit`], including correct rounding.
mod encode;

/// Small fns of one posit argument: neg, prior, next, is_positive, etc.
mod unary;

/// Rounding a posit to integer-valued posit: round_int, floor, ceil.
mod round_int;

/// The four basic arithmetic operations: +, -, ×, ÷.
mod ops;

/// Quire (the fixed-point accumulator for error-free sums and dot products)
pub mod quire;

/// Conversions to and from integers, to and from floats, and between different posit types.
///
/// Two sorts of conversions are implemented:
///   - The conversions prescribed in the posit standard (using `round_from`).
///   - The "Rusty" conversions (using `from` for unfallible conversions and `try_from` for
///     fallible ones).
///
/// The [convert::RoundFrom] and [convert::RoundInto] traits are defined here.
pub mod convert;

/// Traits for [`core::fmt::Display`] and [`core::fmt::Debug`].
mod fmt;

/// Conversions to and from an arbitrary-precision [malachite::rational::Rational], for testing
/// purposes. This enables us to verify our algorithms by checking that the exact rationals match.
/// For example:
///
///   - rational(p1 + p2) = rational(p1) + rational(p2)
///   - rational(p1::ONE) = rational(1)
///   - rational(p1) = rational(decoded(p1))
#[cfg(test)]
mod rational;

/// Miscellaneous helpers for testing.
#[cfg(test)]
mod test;
