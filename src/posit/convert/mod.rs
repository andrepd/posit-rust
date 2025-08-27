use super::*;

// TODO add examples to docs after the impls (for ints, etc) are done

/// Used to do value-to-value conversions that consume the input and **round according to the posit
/// standard**. It is the reciprocal of [`RoundInto`].
///
/// The interface is identical to the standard [`From`], but the conversion is not necessarily
/// lossless, and may round if necessary. For more information, refer to the documentation of
/// [`From`].
///
/// The same guidelines apply: prefer implementing [`RoundFrom`] over [`RoundInto`] because
/// implementing [`RoundFrom`] automatically provides one with an implementation of
/// [`RoundInto`], and prefer using [`RoundInto`] over [`RoundFrom`] in when specifying trait
/// bounds on a generic function. There's also a blanket implementation of `RoundFrom<T> for T`.
pub trait RoundFrom<T> {
  /// Converts to this type from the input type, rounding according to the posit standard if
  /// necessary (round to nearest, ties to even).
  ///
  /// This is a *rounding* conversion that is specified in the posit standard; if you're looking
  /// for the usual Rust-y conversions ([`Into`] if exact, [`TryInto`] if fallible), use those
  /// traits.
  #[must_use]
  fn round_from(value: T) -> Self;
}

/// Used to do value-to-value conversions that consume the input and **round according to the posit
/// standard**. It is the reciprocal of [`RoundFrom`].
///
/// The interface is identical to the standard [`Into`], but the conversion is not necessarily
/// lossless, and may round if necessary. For more information, refer to the documentation of
/// [`Into`].
///
/// The same guidelines apply: prefer implementing [`RoundFrom`] over [`RoundInto`] because
/// implementing [`RoundFrom`] automatically provides one with an implementation of
/// [`RoundInto`], and prefer using [`RoundInto`] over [`RoundFrom`] in when specifying trait
/// bounds on a generic function. There's also a blanket implementation of `RoundInto<T> for T`.
pub trait RoundInto<T> {
  /// Converts this type into the (usually inferred) input type, rounding according to the posit
  /// standard if necessary (round to nearest, ties to even).
  ///
  /// This is a *rounding* conversion that is specified in the posit standard; if you're looking
  /// for the usual Rust-y conversions ([`Into`] if exact, [`TryInto`] if fallible), use those
  /// traits.
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
