import Mathlib

theorem algebra_191686 (a : ℤ) : IsCoprime (a^3 + 2 * a) (a^4 + 3 * a^2 + 1) := by 
  show IsCoprime (a^3 + 2 * a) (a^4 + 3 * a^2 + 1)
  use -(2 * a + a^3), 1 + a^2
  ring