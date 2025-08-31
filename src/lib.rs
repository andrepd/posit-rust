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
//! ```
//! // Use standard posit types, or define your own.
//! # use fast_posit::Posit;
//! use fast_posit::{p8, p16, p32, p64};  // Standard: n bits, 2 exponent bits
//! type MyPosit = Posit<24, 3, i32>;  // Non-standard: 24 bits, 3 exponent bits
//!
//! // Create posits from ints, IEEE floats, strings, constants, or a raw bit representation.
//! # use fast_posit::{RoundFrom, RoundInto};
//! let a = p32::round_from(2.71_f64);
//! let b = p32::round_from(42_i32);
//! let c = p32::from_bits(0x7f001337);
//! let d = p32::MIN_POSITIVE;
//!
//! // Perform basic arithmetic and comparisons with the usual operators.
//! assert!(p16::round_from(2.14_f32) + p16::ONE == 3.14_f32.round_into());
//! assert!(p16::MIN_POSITIVE < 1e-15_f32.round_into());
//!
//! // Convert posits back to ints, IEEE floats, strings, or a raw bit representation.
//! assert_eq!(p8::ONE.to_bits(), 0b01000000)
//! ```
//!
//! # Performance
//!
//! In terms of performance, you can expect as a *very rough estimate* 50 to 80 Mops/s
//! (corresponding to about a 10–20× slowdown relative to native hw FPU operations) on an 11th gen
//! Intel x86 core at 2.80GHz. This is, as far as we're aware, faster (or at least as fast) as any
//! freely available software implementation of posit arithmetic.
//!
//! Needless to say, both absolute performance and relative performance vs the FPU will vary
//! depending on your system.
//!
//! This crate includes benchmarks; run them with `cargo bench -F bench`.

mod posit;
mod underlying;

pub use posit::Posit;
pub use underlying::Int;

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

pub use posit::convert::{RoundFrom, RoundInto};

/// Re-export some internals for benchmarking purposes, only on `feature = "bench"`.
#[cfg(feature = "bench")]
mod bench;
