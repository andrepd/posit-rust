use super::*;

// TODO add examples to docs after the impls (for ints, etc) are done

/// Used to do value-to-value conversions that consume the input and **round according to the posit
/// standard**. It is the reciprocal of [`RoundInto`].
///
/// The interface is identical to the standard [`From`], but the conversion is not necessarily
/// lossless, and may round if necessary. "Rounding" in this crate stands for the [definition in
/// the posit standard]; in short:
///
///   - If the value is greater in absolute value than the biggest posit, round to it.
///   - If the value is smaller in absolute value than the smallest positive posit, round to it.
///   - Otherwise, round to the nearest bit pattern, or in case of a tie, to the even bit pattern.
///
/// For the exact rules, consult the documentation for specific implementations of [`RoundFrom`].
///
/// For more information, refer to the documentation of [`From`]. The same guidelines apply: prefer
/// implementing [`RoundFrom`] over [`RoundInto`] because implementing [`RoundFrom`] automatically
/// provides one with an implementation of[`RoundInto`], and prefer using [`RoundInto`] over
/// [`RoundFrom`] in when specifying trait bounds on a generic function. There's also a blanket
/// implementation of `RoundFrom<T> for T`.
///
/// [definition in the posit standard]: https://posithub.org/docs/posit_standard-2.pdf#section.4
pub trait RoundFrom<T> {
  /// Converts to this type from the input type, [rounding according to the posit standard] if
  /// necessary (round to nearest, ties to even, never over- or under-flow).
  ///
  /// This is a rounding conversion that is specified in the posit standard; if you're looking for
  /// the usual Rust-y conversions ([`Into`] if exact, [`TryInto`] if fallible), use those
  /// traits instead.
  ///
  /// [rounding according to the posit standard]: https://posithub.org/docs/posit_standard-2.pdf#section.4
  #[must_use]
  fn round_from(value: T) -> Self;
}

/// Used to do value-to-value conversions that consume the input and **round according to the posit
/// standard**. It is the reciprocal of [`RoundFrom`].
///
/// The interface is identical to the standard [`Into`], but the conversion is not necessarily
/// lossless, and may round if necessary. "Rounding" in this crate stands for the [definition in
/// the posit standard]:
///
///   - If the value is greater in absolute value than the biggest posit, round to it.
///   - If the value is smaller in absolute value than the smallest positive posit, round to it.
///   - Otherwise, round to the nearest bit pattern, or in case of a tie, to the even bit pattern.
///
/// For more information, refer to the documentation of [`Into`]. The same guidelines apply: prefer
/// implementing [`RoundFrom`] over [`RoundInto`] because implementing [`RoundFrom`] automatically
/// provides one with an implementation of[`RoundInto`], and prefer using [`RoundInto`] over
/// [`RoundFrom`] in when specifying trait bounds on a generic function. There's also a blanket
/// implementation of `RoundInto<T> for T`.
///
/// [definition in the posit standard]: https://posithub.org/docs/posit_standard-2.pdf#section.4
pub trait RoundInto<T> {
  /// Converts this type into the (usually inferred) input type, [rounding according to the posit
  /// standard] if necessary (round to nearest, ties to even, never over- or under-flow).
  ///
  /// This is a rounding conversion that is specified in the posit standard; if you're looking for
  /// the usual Rust-y conversions ([`Into`] if exact, [`TryInto`] if fallible), use those
  /// traits instead.
  ///
  /// [rounding according to the posit standard]: https://posithub.org/docs/posit_standard-2.pdf#section.4
  #[must_use]
  fn round_into(self) -> T;
}

impl<T> RoundFrom<T> for T {
  fn round_from(value: T) -> Self {
    value
  }
}

impl<T, U> RoundInto<U> for T where U: RoundFrom<T> {
  fn round_into(self) -> U {
    U::round_from(self)
  }
}

mod float;
mod int;
mod posit;
