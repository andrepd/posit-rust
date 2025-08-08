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

/// A Posit floating point number with `N` bits and `ES` exponent bits, using `Int` as its
/// underlying type.
///
/// Examples:
///
/// ```
/// # use fast_posit::Posit;
/// type Foo = Posit::<32, 2, i32>;  // A 32-bit posit with 2-bit exponent field, represented in a
///                                  // 32-bit machine type
/// type Bar = Posit::<6, 1, i8>;  // A 6-bit posit with 1-bit exponent field, represented in an
///                                // 8-bit machine type.
/// ```
#[derive(Clone, Copy)]
#[derive(Eq, PartialEq, Ord, PartialOrd, Hash)]  // Eq and Ord are the same as for two's complement int
#[derive(Default)]
pub struct Posit<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> (Int);

/// In order to perform most nontrivial operations, a `Posit<N, ES, Int>` needs to be decoded into
/// a fraction (i.e. mantissa) and an exponent, represented as a `Decoded<N, ES, Int>`. This
/// struct is such that it represents a posit
///
/// ```md
/// `frac` / `FRAC_DENOM` × 2 ^ `exp`
/// ```
///
/// where both `frac` and `exp` are signed `Int`s, and `FRAC_DENOM` is a fixed power of two. See
/// the docstrings for [both](Decoded::frac) [fields](Decoded::exp) for more detail about their
/// values.
///
/// Extracting these fields from a posit, and converting back to a posit with correct rounding, can
/// be done *very* efficiently.
#[derive(Clone, Copy)]
#[derive(Eq, PartialEq, Hash)]
pub struct Decoded<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> {
  pub frac: Int,
  pub exp: Int,
}

/// Some basic constants and functions, such as a check that `N` and `ES` make sense for `Int`, or
/// functions to convert to/from raw bits.
mod basics;

/// Numeric constants: zero, NaR, min, min_positive, etc.
mod consts;

/// [`Posit`] → [`Decoded`].
mod decode;

/// [`Decoded`] → [`Posit`], including correct rounding.
mod encode;

/// Small fns of one posit argument: neg, prior, next, is_positive, etc.
mod unary;

/// Addition and subtraction.
mod add;

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

/// Helper macro for implementing operators for all combinations of value and reference
macro_rules! mk_ops {
  ($trait:ident, $trait_assign:ident, $name:ident, $name_assign:ident) => {
    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait<Posit<N, ES, Int>> for Posit<N, ES, Int> {
      type Output = Posit<N, ES, Int>;

      #[inline]
      fn $name(self, rhs: Self) -> Self::Output { self.$name(rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait<&Posit<N, ES, Int>> for Posit<N, ES, Int> {
      type Output = Posit<N, ES, Int>;

      #[inline]
      fn $name(self, rhs: &Self) -> Self::Output { self.$name(*rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait<Posit<N, ES, Int>> for &Posit<N, ES, Int> {
      type Output = Posit<N, ES, Int>;

      #[inline]
      fn $name(self, rhs: Posit<N, ES, Int>) -> Self::Output { (*self).$name(rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait<&Posit<N, ES, Int>> for &Posit<N, ES, Int> {
      type Output = Posit<N, ES, Int>;

      #[inline]
      fn $name(self, rhs: &Posit<N, ES, Int>) -> Self::Output { (*self).$name(*rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait_assign<Posit<N, ES, Int>> for Posit<N, ES, Int> {
      #[inline]
      fn $name_assign(&mut self, rhs: Posit<N, ES, Int>) { *self = self.$name(rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait_assign<&Posit<N, ES, Int>> for Posit<N, ES, Int> {
      #[inline]
      fn $name_assign(&mut self, rhs: &Posit<N, ES, Int>) { *self = self.$name(*rhs) }
    }
  }
}

pub(crate) use mk_ops;
