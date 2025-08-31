use super::*;

/// Addition and subtraction (both use the same addition algorithm, and `a - b` is simply
/// `a + (-b)`.
mod add;

/// Multiplication.
mod mul;

/// Division.
mod div;

/// Helper macro for implementing operators for all combinations of value and reference
macro_rules! mk_ops {
  ($trait:ident, $trait_assign:ident, $name:ident, $name_assign:ident) => {
    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait<Posit<N, ES, Int>> for Posit<N, ES, Int> {
      type Output = Posit<N, ES, Int>;

      #[inline]
      fn $name(self, rhs: Self) -> Self::Output { self.$name(rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait<&Posit<N, ES, Int>> for Posit<N, ES, Int> {
      type Output = Posit<N, ES, Int>;

      #[inline]
      fn $name(self, rhs: &Self) -> Self::Output { self.$name(*rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait<Posit<N, ES, Int>> for &Posit<N, ES, Int> {
      type Output = Posit<N, ES, Int>;

      #[inline]
      fn $name(self, rhs: Posit<N, ES, Int>) -> Self::Output { (*self).$name(rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait<&Posit<N, ES, Int>> for &Posit<N, ES, Int> {
      type Output = Posit<N, ES, Int>;

      #[inline]
      fn $name(self, rhs: &Posit<N, ES, Int>) -> Self::Output { (*self).$name(*rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait_assign<Posit<N, ES, Int>> for Posit<N, ES, Int> {
      #[inline]
      fn $name_assign(&mut self, rhs: Posit<N, ES, Int>) { *self = self.$name(rhs) }
    }

    impl<const N: u32, const ES: u32, Int: crate::Int>
    $trait_assign<&Posit<N, ES, Int>> for Posit<N, ES, Int> {
      #[inline]
      fn $name_assign(&mut self, rhs: &Posit<N, ES, Int>) { *self = self.$name(*rhs) }
    }
  }
}

pub(crate) use mk_ops;

