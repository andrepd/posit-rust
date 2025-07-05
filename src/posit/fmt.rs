use super::*;

use core::fmt::Debug;

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Debug for Posit<N, ES, Int> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    if const { Self::JUNK_BITS == 0 } {
      let bits = self.0;
      f.debug_tuple("Posit")
        .field(&format_args!("0b{bits:0w$b}", w=Int::BITS as usize))
        .finish()
    } else {
      let bits_junk = (self.0 >> Self::BITS).mask_lsb(Self::JUNK_BITS);
      let bits_significant = self.0.mask_lsb(Self::BITS);
      f.debug_tuple("Posit")
        .field(&format_args!("0b{bits_junk:0wj$b}_{bits_significant:0ws$b}", wj=Self::JUNK_BITS as usize, ws=Self::BITS as usize))
        .finish()
    }
  }
}

impl<
  const N: u32,
  const ES: u32,
  Int: crate::Int,
> Debug for Decoded<N, ES, Int> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let frac_hidden = self.frac.lshr(Int::BITS - 2);
    let frac_explicit = (self.frac << 2).lshr(3);
    let frac_round = self.frac & Int::ONE;
    let exp_regime = self.exp.lshr(ES);
    let exp_exponent = self.exp.mask_lsb(ES);
    let exp_total = self.exp;
    f.debug_struct("Decoded")
      .field("frac", &format_args!("0b{frac_hidden:02b}_{frac_explicit:0w$b}_{frac_round:b}",
        w=Int::BITS as usize - 3
      ))
      .field("exp", &format_args!("0b{exp_regime:0wr$b}_{exp_exponent:0we$b} ({exp_total:+})",
        wr=(Int::BITS - ES) as usize, we=ES as usize,
      ))
      .finish()
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn posit_nojunk() {
    assert_eq!(
      format!("{:?}", Posit::<8, 2, i8>::from_bits_unsigned(0b00101011)).as_str(),
      "Posit(0b00101011)",
    );
    assert_eq!(
      format!("{:?}", Posit::<8, 2, i8>::from_bits_unsigned(0b10101011)).as_str(),
      "Posit(0b10101011)",
    );
  }

  #[test]
  fn posit_junk() {
    assert_eq!(
      format!("{:?}", Posit::<6, 2, i16>::from_bits_unsigned(0b001011)).as_str(),
      "Posit(0b0000000000_001011)",
    );
    assert_eq!(
      format!("{:?}", Posit::<6, 2, i16>::from_bits_unsigned(0b101011)).as_str(),
      "Posit(0b1111111111_101011)",
    );
  }

  #[test]
  fn decoded() {
    assert_eq!(
      format!("{:?}", Decoded::<6, 2, i16>{ frac: 0b01_0010101110110_0, exp: 3 }).as_str(),
      "Decoded { frac: 0b01_0010101110110_0, exp: 0b00000000000000_11 (+3) }",
    );
    assert_eq!(
      format!("{:?}", Decoded::<6, 2, i16>{ frac: -0b01_0010101110110_0, exp: 3 }).as_str(),
      "Decoded { frac: 0b10_1101010001010_0, exp: 0b00000000000000_11 (+3) }",
    );
    assert_eq!(
      format!("{:?}", Decoded::<6, 2, i16>{ frac: 0b01_0000000000000_1, exp: -1 }).as_str(),
      "Decoded { frac: 0b01_0000000000000_1, exp: 0b11111111111111_11 (-1) }",
    );
    assert_eq!(
      format!("{:?}", Decoded::<6, 4, i16>{ frac: 0b01_0000000000000_1, exp: -20 }).as_str(),
      "Decoded { frac: 0b01_0000000000000_1, exp: 0b111111111110_1100 (-20) }",
    );
  }
}
