// Source: https://github.com/stillwater-sc/universal/

#![allow(non_camel_case_types)]

use fast_posit::{p32, p64};

#[repr(C)]
#[derive(Clone, Copy)]
pub struct posit32_t { v: u32 }

#[repr(C)]
#[derive(Clone, Copy)]
pub struct posit64_t { v: u64 }

#[link(name = "posit_c_api_shim")]
unsafe extern "C" {
  pub fn posit32_addp32(x: posit32_t, y: posit32_t) -> posit32_t;
  pub fn posit64_addp64(x: posit64_t, y: posit64_t) -> posit64_t;
}

impl From<p32> for posit32_t { fn from(x: p32) -> Self { posit32_t { v: x.to_bits() as u32 } } }
impl From<p64> for posit64_t { fn from(x: p64) -> Self { posit64_t { v: x.to_bits() as u64 } } }

impl From<posit32_t> for p32 { fn from(x: posit32_t) -> Self { Self::from_bits(x.v as i32) } }
impl From<posit64_t> for p64 { fn from(x: posit64_t) -> Self { Self::from_bits(x.v as i64) } }

// TODO unit test that these agree with our impl
