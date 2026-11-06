import Mathlib

theorem algebra_256304 (a : ℤ) (ha : a ≠ 0) :
    IsCoprime (a^3 + 2 * a) (a^4 + 3 * a^2 + 1) := by 
  show IsCoprime (a^3 + 2 * a) (a^4 + 3 * a^2 + 1)
  use (-a^3 - 2 * a)
  use (1 + a^2)
  ring_nf