**🚧 Work in progress! 🚧**

# fast-posit

Software implementation of [Posit arithmetic](https://posithub.org/docs/Posits4.pdf) in Rust.
Correct, clean, and 🚀 *fast*.

## Introduction

Posits are an alternative floating point format proposed by John Gustafson in 2017, with the first
published standard in 2022. They have several interesting features that make them an excellent
replacement for traditional IEEE754 floats, in domains such as neural networks or HPC.

Some highlights of the Posit format:

- Generally higher accuracy and/or dynamic range for the *same number of bits* (e.g. 32-bit posits
  are often a suitable replacement for 64-bit floats). Posits have a *smaller* decimal error for
  the overwhelming majority of operations (+, ×, sqrt, etc) compared to IEEE724 floats of the
  same size.
- Tapered accuracy, elegantly allocating more bits to the mantissa for values close to ±1,
  and gradually decreasing the precision as the absolute value of the exponent increases.
- The ability to calculate sums and dot products with up to $2^{30}$ terms very fast and with NO
  intermediate rounding whatsoever!
- Flexibility to choose any bit width ≥ 2 and any exponent width ≤ bit width, tailored to the
  parameters of your application: accuracy, dynamic range, memory constraints, etc.
- Simple and deterministic rounding, with bounded errors, and no infinite loss of precision via
  under- and over-flows, in any circumstance.
- No signed zero, no quadrillions of NaNs, no subnormals, no redundant bit patterns, no exceptions.
  Just one 0, one NaN, and regular numbers. This is not only simpler to reason about and debug,
  but also unlocks faster software implementations and less power-hungry hardware
  implementations.
- Many other goodies: deterministic and correct elementary functions in the standard, a blazing
  fast sigmoid for ML, etc.

Posits are pretty cool, you should read about them [here](https://posithub.org/docs/Posits4.pdf) or
[here](https://posithub.org/docs/posit_standard-2.pdf) or
[here](https://groups.google.com/g/unum-computing).

This crate has the following objectives, in order of importance:

- **Correctness**: all functions are correct as defined in [the standard]
  (https://posithub.org/docs/posit_standard-2.pdf) (i.e. they give the *correct results*, for *all
  inputs*, with the *correct rounding*). This is verified by extensive built-in tests that check
  all operations against an oracle (which uses arbitrary precision arithmetic to calculate the
  correct unrounded result), exhaustively where possible, and probabilistically where we cannot
  enumerate all inputs.
- **Performance**: this library is to the best of our knowledge faster than, or at least as fast
  as, any freely available software implementation of posits. We include benchmarks that check our
  implementation against various external ones; see below for how to run them.
- **Readability**: Nonwithstanding a fast implementation being quite byzantine and difficult to
  understand at first glance, the code is well structured and *extensively* documented. If you are
  interested in learning more about posits, or about software implementation of floating point
  formats in general, you may benefit from reading through this code!

## Usage

```rust
// TODO
```

## Testing

Run tests with `cargo test`.

## Benchmarks

Run benchmarks with `cargo bench -F bench`.

Benchmarks which test against external implementations need to be enabled with feature flags, e.g.
`cargo bench -F bench,cerlane-softposit,berkeley-softfloat`.

Mind that the relevant C library needs to be available to the linker; if they are not in the
standard paths you may need to set `RUSTFLAGS="-L /path/to/lib"`.

## Features

- [x] Posits with arbitrary size and arbitrary exponent size
- [x] Basic arithmetic (+, -, ×, ÷)
- [ ] Elementary functions (sqrt, exp)
  - [ ] Exponentiation (sqrt, pow, hypot, etc)
  - [ ] Exponentials and logarithms (exp, log, exp2, logPlus1, etc)
  - [ ] Trigonometry (sin, cos, asin, cosh, etc)
- [ ] Conversions
- [ ] Parsing and printing
- [ ] Quire

## Dependencies

This crate has no (non-dev) dependencies, and can be used in `no_std` contexts.
