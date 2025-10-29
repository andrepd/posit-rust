use super::*;

// TODO add examples to docs after the impls (for ints, etc) are done

/// Used to do value-to-value conversions using the rules prescribed for that conversion in the
/// [posit standard], which may *round* the input (see below). It is the reciprocal of
/// [`RoundInto`].
///
/// The interface is identical to the standard [`From`], but for the [conversions described in the
/// posit standard]; therefore — unlike that which is the
/// [convention for the `From` trait](core::convert::From#when-to-implement-from) —
/// these conversions are _not necessarily lossless_, and may round if necessary, according the
/// [definition in the posit standard].
///
/// The exact meaning of these conversions depends on the types involved; for the exact description
/// of what each particular conversion does, **consult the documentation for specific
/// implementations of `round_from`**.
///
/// Many of the usage guidelines for [`From`] also apply to [`RoundFrom`]: if you do implement it
/// for your types, prefer implementing [`RoundFrom`] over [`RoundInto`] because implementing
/// [`RoundFrom`] automatically provides one with an implementation of [`RoundInto`], and prefer
/// using [`RoundInto`] over [`RoundFrom`] when specifying trait bounds on a generic function.
/// There's also a blanket implementation of `RoundFrom<T> for T`, and `RoundFrom<T> for U`
/// implies `RoundInto<U> for T`.
///
/// # Rounding
///
/// "Rounding" in this crate stands for the [definition in the posit standard]. In short:
///
///   - If the value is greater in absolute value than the biggest posit, round to it (i.e., never
///     overflow).
///   - If the value is smaller in absolute value than the smallest positive posit, round to it
///     (i.e., never underflow).
///   - Otherwise, round to the nearest bit pattern, or in case of a tie, to the even bit pattern.
///
/// # Examples
///
/// Rounding from ints, floats:
/// ```
/// # use fast_posit::*;
/// assert!(p16::round_from(1) == p16::round_from(1.00000001));
/// assert!(p32::round_from(1) <  p32::round_from(1.00000001));
///
/// assert_eq!(p32::round_from(f64::NAN), p32::NAR);
/// ```
///
/// Rounding to ints, floats:
/// ```
/// # use fast_posit::*;
/// assert_eq!(f32::round_from(p16::MIN_POSITIVE), 1.3877788e-17);
/// assert_eq!(i64::round_from(p8::MAX), 1 << 24);
///
/// assert!(f64::round_from(p32::NAR).is_nan());
/// ```
///
/// [posit standard]: https://posithub.org/docs/posit_standard-2.pdf#section.6
/// [conversions described in the posit standard]: https://posithub.org/docs/posit_standard-2.pdf#section.6
/// [definition in the posit standard]: https://posithub.org/docs/posit_standard-2.pdf#section.4
pub trait RoundFrom<T> {
  /// Converts to this type from the input type, [according to the rules prescribed in the posit
  /// standard] for this particular conversion.
  ///
  /// This is the _rounding_ conversion that is specified in the posit standard (see
  /// [Rounding](RoundFrom#rounding)); if you're looking for the usual Rust-y conversions
  /// ([`From`] if exact, [`TryFrom`] if fallible), use those traits instead.
  ///
  /// [according to the rules prescribed in the posit standard]: https://posithub.org/docs/posit_standard-2.pdf#section.4
  #[must_use]
  fn round_from(value: T) -> Self;
}

/// Used to do value-to-value conversions using the rules prescribed for that conversion in the
/// [posit standard], which may *round* the input (see below). It is the reciprocal of
/// [`RoundFrom`].
///
/// The interface is identical to the standard [`Into`], but for the [conversions described in the
/// posit standard]; therefore — unlike that which is the
/// [convention for the `From` and `Into` traits](core::convert::From#when-to-implement-from) —
/// these conversions are _not necessarily lossless_, and may round if necessary, according the
/// [definition in the posit standard].
///
/// The exact meaning of these conversions depends on the types involved; for the exact description
/// of what each particular conversion does, **consult the documentation for specific
/// implementations of `round_from`**.
///
/// Many of the usage guidelines for [`Into`] also apply to [`RoundInto`]: if you do implement it
/// for your types, prefer implementing [`RoundFrom`] over [`RoundInto`] because implementing
/// [`RoundFrom`] automatically provides one with an implementation of [`RoundInto`], and prefer
/// using [`RoundInto`] over [`RoundFrom`] when specifying trait bounds on a generic function.
/// There's also a blanket implementation of `RoundInto<T> for T`, and `RoundFrom<T> for U`
/// implies `RoundInto<U> for T`.
///
/// # Rounding
///
/// "Rounding" in this crate stands for the [definition in the posit standard]. In short:
///
///   - If the value is greater in absolute value than the biggest posit, round to it (i.e., never
///     overflow).
///   - If the value is smaller in absolute value than the smallest positive posit, round to it
///     (i.e., never underflow).
///   - Otherwise, round to the nearest bit pattern, or in case of a tie, to the even bit pattern.
///
/// # Examples
///
/// Rounding from ints, floats:
/// ```
/// # use fast_posit::*;
/// assert_eq!(p16::ONE.next(), 1.0004883_f64.round_into());
/// assert_eq!(p32::ONE.next(), 1.0000000075_f64.round_into());
///
/// assert_eq!(p32::NAR, f64::NAN.round_into());
/// ```
///
/// Rounding to ints, floats:
/// ```
/// # use fast_posit::*;
/// assert_eq!(5.960464477539063e-8, p8::MIN_POSITIVE.round_into());
/// assert_eq!(1_i64 << 56, p16::MAX.round_into());
///
/// assert!(f64::is_nan(p32::NAR.round_into()));
/// ```
///
/// [posit standard]: https://posithub.org/docs/posit_standard-2.pdf#section.6
/// [conversions described in the posit standard]: https://posithub.org/docs/posit_standard-2.pdf#section.6
/// [definition in the posit standard]: https://posithub.org/docs/posit_standard-2.pdf#section.4
pub trait RoundInto<T> {
  /// Converts this type into the (usually inferred) input type, [according to the rules prescribed
  /// in the posit standard] for this particular conversion.
  ///
  /// This is the _rounding_ conversion that is specified in the posit standard (see
  /// [Rounding](RoundInto#rounding)); if you're looking for the usual Rust-y conversions
  /// ([`Into`] if exact, [`TryInto`] if fallible), use those traits instead.
  ///
  /// [according to the rules prescribed in the posit standard]: https://posithub.org/docs/posit_standard-2.pdf#section.4
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
