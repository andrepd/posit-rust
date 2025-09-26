![Github CI status](https://img.shields.io/github/actions/workflow/status/andrepd/posit-rust/ci.yml)
![crates.io](https://img.shields.io/crates/v/fast_posit)
![docs.rs](https://img.shields.io/docsrs/fast_posit)

**🚧 Work in progress! 🚧**

# fast-posit

Software implementation of [Posit arithmetic](https://posithub.org/docs/Posits4.pdf) in Rust.
Correct, clean, and 🚀 *fast*.

## Introduction

Posits are an alternative floating point format proposed by John Gustafson in 2017, with the first
published standard in 2022. They have several interesting features that make them an excellent
replacement for traditional IEEE754 floats, in domains such as neural networks or HPC.

Some highlights of the Posit format:

- Generally higher accuracy and/or dynamic range for the *same number of bits*, as compared to IEEE
  floats. Posits have a *smaller* decimal error for the majority of operations (+, ×, sqrt, etc)
  compared to a IEEE float of the same size.
- Simple and deterministic rounding, with bounded errors, and no infinite loss of precision via
  under- and over-flows, in any circumstance. Unlike IEEE floats, all operations are
  deterministic, portable, and *fully reproducible* across systems.
- Tapered accuracy, elegantly allocating more bits to the mantissa for values close to ±1,
  and gradually decreasing the precision as the absolute value of the exponent increases.
- The ability to calculate sums and dot products with up to $2^{30}$ terms very fast and with NO
  intermediate rounding whatsoever, even with parallelisation!
- Flexibility to choose any bit width ≥ 2 and any exponent width ≤ bit width, tailored to the
  parameters of your application: accuracy, dynamic range, memory constraints, etc.
- No signed zero, no quadrillions of NaNs, no subnormals, no redundant bit patterns, no exceptions.
  Just one 0, one NaN, and regular numbers. This is not only simpler to reason about and debug,
  but also unlocks faster software implementations and less power-hungry hardware
  implementations.
- Many other niceties: standard-mandated elementary functions with correct rounding, first-class
  support for mixed-precision, a blazing fast sigmoid for ML, etc.

Posits are pretty cool, you should read about them [here](https://posithub.org/docs/Posits4.pdf) or
[here](https://posithub.org/docs/posit_standard-2.pdf) or
[here](https://groups.google.com/g/unum-computing).

This crate has the following objectives, in order of importance:

- **Correctness**: all functions are correct as defined in [the standard] (i.e. they give
  the *correct results*, for *all inputs*, with the *correct rounding*). This is verified by
  extensive built-in tests that check all operations against an oracle (which uses arbitrary
  precision arithmetic to calculate the correct unrounded result), exhaustively where possible,
  and probabilistically where we cannot enumerate all inputs.
- **Performance**: this library is to the best of our knowledge faster than, or at least as fast
  as, any freely available software implementation of posits. We include benchmarks that check our
  implementation against various external ones; see below for how to run them.
- **Readability**: Nonwithstanding a fast implementation being quite byzantine and difficult to
  understand at first glance, the code is well structured and *extensively* documented. If you are
  interested in learning more about posits, or about software implementation of floating point
  formats in general, you may benefit from reading through this code!

This crate aims to implement the entire posit standard and beyond, including features such as
arbitrary posit and quire sizes beyond those prescribed by the standard. Versions prior to 1.0.0,
however, may be incomplete.

## Usage

The following is an extended tour over the main functionality of the crate, sort of in the style
of "learn X in Y minutes". For more information, refer to the documentation of specific types and
functions.

```rust
// Use standard posit types, or define your own.
use fast_posit::{p8, p16, p32, p64};  // Standard: n bits, 2 exponent bits
type MyPosit = Posit<24, 3, i32>;  // Non-standard: 24 bits, 3 exponent bits

// Create posits from ints, IEEE floats, strings, constants, or a raw bit representation.
let a = p32::round_from(2.71_f64);
let b = p32::round_from(42_i32);
let c = p32::from_bits(0x7f001337);
let d = p32::MIN_POSITIVE;

// Perform basic arithmetic and comparisons using the usual operators.
assert!(p16::round_from(2.14) + p16::ONE == p16::round_from(3.14));
assert!(p16::MIN_POSITIVE < 1e-15.round_into());

// Convert posits back to ints, IEEE floats, strings, or a raw bit representation.
assert_eq!(p8::ONE.to_bits(), 0b01000000);

// Use a quire to calculate sums and dot products _without loss of precision_!
use fast_posit::{q8, q16, q32, q64};
let mut quire = q16::ZERO;
quire += p16::MAX;
quire += p16::round_from(0.1);
quire -= p16::MAX;
let result: p16 = (&quire).round_into();
// Correct result with the quire, no issues with rounding errors.
assert_eq!(result, p16::round_from(0.1))
// The same sum without the quire would give a wrong result, due to double rounding.
let posit = p16::MAX + p16::round_from(0.1) - p16::MAX;
assert_eq!(posit, p16::ZERO);

// Use a quire per thread to ensure the result is the same regardless of parallelisation!
let mut quires = [q16::ZERO; 8];
for thread in 0..8 {
  let local_quire = &mut quires[thread];
  *local_quire += p16::round_from(123);
  *local_quire += p16::round_from(456);
  // ...
}
// Assemble the final result by summing the thread-local quires first, then converting to posit.
for thread in 1..8 {
  quires[0] += quire[thread]
}
let result: p16 = (&quires[0]).round_into();

// Use mixed-precision with no hassle; it's very cheap when the ES is the same.
let terms = [3, 7, 15, 1].map(p8::round_from);
let pi = {
  let mut partial = p64::ZERO;
  for i in terms[1..].iter().rev() {
    partial = p64::ONE / (i.convert() + partial)
  }
  terms[0].convert() + partial
};
assert!((3.141592.round_into() .. 3.141593.round_into()).contains(&pi));
```

## Performance

In terms of performance, you can expect as a *very rough estimate* 50 to 250 Mops/s (corresponding
to about a 4–20× slowdown relative to native hw FPU operations) on an 11th gen Intel x86 core at
2.80GHz. Needless to say, both absolute performance and relative performance vs the FPU will vary
depending on your system. See below for how to run benchmarks.

## Testing

Run tests with `cargo test`.

The test suite is very comprehensive. Testing is exhaustive where feasible, and probabilistic where
not. Emphasis is put on the standard types, but also on various other combinations of parameters.
Since the implementations are generic, this gives a high degree of confidence that all
combinations of parameters are bug-free.

## Benchmarks

Run benchmarks with `cargo bench -F bench`.

Benchmarks which test against external implementations need to be enabled with feature flags, e.g.
`cargo bench -F bench,cerlane-softposit,berkeley-softfloat`.

Mind that the relevant C library needs to be available to the linker; if they are not in the
standard paths you may need to set `RUSTFLAGS="-L /path/to/lib"`.

## Features

- [x] Posits with arbitrary size and arbitrary exponent size
- [ ] Basics
  - [x] Arithmetic (+, -, ×, ÷)
  - [x] Comparisons (>, ==, …)
  - [ ] Rounding to integer (floor, ceil, …)
- [ ] Elementary functions
  - [ ] Exponentials and logarithms (exp, log, exp2, logPlus1, …)
  - [ ] Trigonometry (sin, cos, asin, …)
  - [ ] Hyperbolics (sinh, cosh, asinh, …)
  - [ ] Exponentiation (sqrt, pow, hypot, …)
- [ ] Conversions
  - [ ] To integers
  - [x] From integers
  - [ ] To floats
  - [x] From floats
  - [x] To/from posits
- [ ] Parsing and printing
- [ ] Quire
  - [x] Loading/storing
  - [x] Adding posits
  - [ ] Adding products of posits
  - [ ] Adding quires

## Dependencies

This crate has no (non-dev) dependencies, and can be used in `no_std` contexts.

[the standard]: https://posithub.org/docs/posit_standard-2.pdf
