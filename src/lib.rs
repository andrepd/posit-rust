#![cfg_attr(not(test), no_std)]

mod posit;
mod underlying;

pub use posit::Posit;
pub use underlying::Int;

/// Standard-compliant 8-bit posit.
#[allow(non_camel_case_types)]
pub type p8 = Posit<8, 2, i8>;

/// Standard-compliant 16-bit posit.
#[allow(non_camel_case_types)]
pub type p16 = Posit<16, 2, i16>;

/// Standard-compliant 32-bit posit.
#[allow(non_camel_case_types)]
pub type p32 = Posit<32, 2, i32>;

/// Standard-compliant 64-bit posit.
#[allow(non_camel_case_types)]
pub type p64 = Posit<64, 2, i64>;

/// Re-export some internals for benchmarking purposes, only on `feature = "bench"`.
#[cfg(feature = "bench")]
mod bench;
