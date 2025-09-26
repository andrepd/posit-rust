use super::*;

// The `Int` trait has bounds indirectly, via `Sealed`. For example, we don't have `Int:
// PartialEq`, we have `Int: Sealed` and `Sealed: PartialEq`, so the derive macro derives
//
//   impl<const N: u32, const ES: u32, Int: PartialEq + Int> PartialEq for Posit<N, ES, Int>
//
// but of course we know we can just have
//
//   impl<const N: u32, const ES: u32, Int: Int> PartialEq for Posit<N, ES, Int>
//
// Because of that we just implement explicitly here.

impl<const N: u32, const ES: u32, Int: crate::Int>
Clone for Posit<N, ES, Int> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0)
  }
}

impl<const N: u32, const ES: u32, Int: crate::Int>
Copy for Posit<N, ES, Int> {}

impl<const N: u32, const ES: u32, Int: crate::Int>
PartialEq for Posit<N, ES, Int> {
  #[inline]
  fn eq(&self, other: &Self) -> bool {
    self.0 == other.0
  }
}

impl<const N: u32, const ES: u32, Int: crate::Int>
Eq for Posit<N, ES, Int> {}

impl<const N: u32, const ES: u32, Int: crate::Int>
PartialOrd for Posit<N, ES, Int> {
  #[inline]
  fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
    self.0.partial_cmp(&other.0)
  }
}

impl<const N: u32, const ES: u32, Int: crate::Int>
Ord for Posit<N, ES, Int> {
  #[inline]
  fn cmp(&self, other: &Self) -> core::cmp::Ordering {
    self.0.cmp(&other.0)
  }
}

impl<const N: u32, const ES: u32, Int: crate::Int>
core::hash::Hash for Posit<N, ES, Int> {
  #[inline]
  fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
    self.0.hash(state);
  }
}

impl<const N: u32, const ES: u32, Int: crate::Int>
Default for Posit<N, ES, Int> {
  #[inline]
  fn default() -> Self {
    Self(Default::default())
  }
}
