// Source: https://gitlab.com/cerlane/SoftPosit

#![allow(non_camel_case_types)]

use fast_posit::{p32, p64};

#[repr(C)]
#[derive(Clone, Copy)]
pub struct posit32_t { v: u32 }

#[repr(C)]
#[derive(Clone, Copy)]
pub struct posit64_t { v: u64 }

#[link(name = "softposit")]
unsafe extern "C" {
  pub fn p32_add(x: posit32_t, y: posit32_t) -> posit32_t;
  // pub fn p64_add(x: posit64_t, y: posit64_t) -> posit64_t;

  pub fn p32_mul(x: posit32_t, y: posit32_t) -> posit32_t;
  // pub fn p64_mul(x: posit64_t, y: posit64_t) -> posit64_t;

  pub fn p32_div(x: posit32_t, y: posit32_t) -> posit32_t;
  // pub fn p64_div(x: posit64_t, y: posit64_t) -> posit64_t;

  pub fn p32_sqrt(x: posit32_t) -> posit32_t;
  // pub fn p64_sqrt(x: posit64_t) -> posit64_t;
}

impl From<p32> for posit32_t { fn from(x: p32) -> Self { posit32_t { v: x.to_bits() as u32 } } }
impl From<p64> for posit64_t { fn from(x: p64) -> Self { posit64_t { v: x.to_bits() as u64 } } }

impl From<posit32_t> for p32 { fn from(x: posit32_t) -> Self { Self::from_bits(x.v as i32) } }
impl From<posit64_t> for p64 { fn from(x: posit64_t) -> Self { Self::from_bits(x.v as i64) } }
