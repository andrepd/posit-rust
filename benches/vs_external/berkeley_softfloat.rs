// Source: https://www.jhauser.us/arithmetic/SoftFloat.html

#![allow(non_camel_case_types)]

#[repr(C)]
#[derive(Clone, Copy)]
pub struct float32_t { v: u32 }

#[repr(C)]
#[derive(Clone, Copy)]
pub struct float64_t { v: u64 }

#[link(name = "softfloat")]
unsafe extern "C" {
  pub fn f32_add(x: float32_t, y: float32_t) -> float32_t;
  pub fn f64_add(x: float64_t, y: float64_t) -> float64_t;

  pub fn f32_mul(x: float32_t, y: float32_t) -> float32_t;
  pub fn f64_mul(x: float64_t, y: float64_t) -> float64_t;

  pub fn f32_div(x: float32_t, y: float32_t) -> float32_t;
  pub fn f64_div(x: float64_t, y: float64_t) -> float64_t;

  pub fn f32_sqrt(x: float32_t) -> float32_t;
  pub fn f64_sqrt(x: float64_t) -> float64_t;
}

impl From<f32> for float32_t { fn from(x: f32) -> Self { float32_t { v: x.to_bits() } } }
impl From<f64> for float64_t { fn from(x: f64) -> Self { float64_t { v: x.to_bits() } } }

impl From<float32_t> for f32 { fn from(x: float32_t) -> Self { Self::from_bits(x.v) } }
impl From<float64_t> for f64 { fn from(x: float64_t) -> Self { Self::from_bits(x.v) } }
