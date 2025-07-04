#![cfg_attr(not(test), no_std)]

mod posit;
mod underlying;

pub use posit::Posit;
pub use underlying::Int;
