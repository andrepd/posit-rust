#![cfg_attr(not(test), no_std)]

//! This crate provides a correct, clean, flexible, and 🚀 *fast* software implementation of
//! [Posit arithmetic](https://posithub.org/docs/posit_standard-2.pdf).
//!
//! # Introduction
//!
//! Posits are an alternative floating point format proposed by John Gustafson in 2017, with the
//! first published standard in 2022. They have several interesting features that make them an
//! excellent replacement for traditional IEEE754 floats, in domains such as neural networks or
//! HPC.
//!
//! The following references are useful if you are not yet familiar with posits:
//!
//!   - [Posit standard](https://posithub.org/docs/posit_standard-2.pdf) (2022)
//!   - [Original extended paper](https://posithub.org/docs/Posits4.pdf) (2017)
//!   - [Book](https://doi.org/10.1201/9781003466024 ) (2024)
//!
//! This crate aims to implement the entire posit standard and beyond, including features such as
//! arbitrary posit and quire sizes beyond those prescribed by the standard. Versions prior to
//! 1.0.0, however, may be incomplete. Correctness is ensured via extensive testing against an
//! oracle.
//!
//! # Usage
//!
//! The following is an extended tour over the main functionality of the crate, sort of in the
//! style of "learn X in Y minutes". For more information, refer to the documentation of specific
//! types and functions.
//!
//! Wherever a function corresponds to a function in 
//! [the standard](https://posithub.org/docs/posit_standard-2.pdf), it will be marked accordingly
//! in its documentation.
//!
//! ```
//! // Use standard posit types, or define your own.
//! # use fast_posit::Posit;
//! use fast_posit::{p8, p16, p32, p64};  // Standard: n bits, 2 exponent bits
//! type MyPosit = Posit<24, 3, i32>;  // Non-standard: 24 bits, 3 exponent bits
//!
//! // Create posits from ints, IEEE floats, strings, constants, or a raw bit representation.
//! use fast_posit::{RoundFrom, RoundInto};
//! let a = p32::round_from(2.71_f64);
//! let b = p32::round_from(42_i32);
//! let c = p32::from_bits(0x7f001337);
//! let d = p32::MIN_POSITIVE;
//!
//! // Perform basic arithmetic and comparisons using the usual operators.
//! assert!(p16::round_from(2.14) + p16::ONE == p16::round_from(3.14));
//! assert!(p16::MIN_POSITIVE < 1e-15.round_into());
//!
//! // Convert posits back to ints, IEEE floats, strings, or a raw bit representation.
//! assert_eq!(p8::ONE.to_bits(), 0b01000000);
//!
//! // Use a quire to calculate sums and dot products _without loss of precision_!
//! use fast_posit::{q8, q16, q32, q64};
//! let mut quire = q16::ZERO;  
//! quire += p16::MAX;
//! quire += p16::round_from(0.1);
//! quire -= p16::MAX;
//! let result: p16 = (&quire).round_into();
//! // Correct result with the quire, no issues with rounding errors.
//! assert_eq!(result, p16::round_from(0.1));
//! // The same sum without the quire would give a wrong result, due to double rounding.
//! let posit = p16::MAX + p16::round_from(0.1) - p16::MAX;
//! assert_eq!(posit, p16::ZERO);
//!
//! // Use a quire per thread to ensure the result is the same regardless of parallelisation!
//! let mut quires = [q16::ZERO; 8];
//! for thread in 0..8 {
//!   let local_quire = &mut quires[thread];
//!   *local_quire += p16::round_from(123);
//!   *local_quire += p16::round_from(456);
//!   // ...
//! }
//! // Assemble the final result by summing the thread-local quires first, then converting to posit.
//! //TODO for thread in 1..8 {
//! //TODO   quires[0] += quire[thread]
//! //TODO }
//! let result: p16 = (&quires[0]).round_into();
//!
//! // Use mixed-precision with no hassle; it's very cheap when the ES is the same.
//! //TODO let mut quire = q64::ZERO;
//! //TODO quire += q64::from(42);
//! //TODO quire += q8::round_from(12).into();
//! ```
//!
//! # Performance
//!
//! In terms of performance, you can expect as a *very rough estimate* 50 to 250 Mops/s
//! (corresponding to about a 4–20× slowdown relative to native hw FPU operations) on an 11th gen
//! Intel x86 core at 2.80GHz. This is, as far as we're aware, faster (or at least as fast) than
//! any freely available software implementation of posit arithmetic.
//!
//! Needless to say, both absolute performance and relative performance vs the FPU will vary
//! depending on your system.
//!
//! This crate includes benchmarks; run them with `cargo bench -F bench`.

mod posit;
mod underlying;

pub use posit::Posit;
pub use posit::quire::Quire;
pub use underlying::Int;
pub use posit::convert::{RoundFrom, RoundInto};

/// Standard-defined 8-bit posit (with 2-bit exponent).
#[allow(non_camel_case_types)]
pub type p8 = Posit<8, 2, i8>;

/// Standard-defined 16-bit posit (with 2-bit exponent).
#[allow(non_camel_case_types)]
pub type p16 = Posit<16, 2, i16>;

/// Standard-defined 32-bit posit (with 2-bit exponent).
#[allow(non_camel_case_types)]
pub type p32 = Posit<32, 2, i32>;

/// Standard-defined 64-bit posit (with 2-bit exponent).
#[allow(non_camel_case_types)]
pub type p64 = Posit<64, 2, i64>;

/// Standard-defined 128-bit quire for a [p8].
#[allow(non_camel_case_types)]
pub type q8 = Quire<8, 2, 16>;

/// Standard-defined 256-bit quire for a [p16].
#[allow(non_camel_case_types)]
pub type q16 = Quire<16, 2, 32>;

/// Standard-defined 512-bit quire for a [p32].
#[allow(non_camel_case_types)]
pub type q32 = Quire<32, 2, 64>;

/// Standard-defined 1024-bit quire for a [p64].
#[allow(non_camel_case_types)]
pub type q64 = Quire<64, 2, 128>;

/// Re-export some internals for benchmarking purposes, only on `feature = "bench"`.
#[cfg(feature = "bench")]
mod bench;

/// Set the number of proptest cases globally.
///
/// This number strikes a balance between coverage and practicality.
#[cfg(test)]
const PROPTEST_CASES: u32 = if cfg!(debug_assertions) {0x1_0000} else {0x80_0000};
