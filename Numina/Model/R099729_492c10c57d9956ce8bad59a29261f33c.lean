import Mathlib

theorem number_theory_101783 (n : ℤ) : IsCoprime (39*n+4) (26*n+3) := by
  show IsCoprime (39 * n + 4) (26 * n + 3)
  use -2, 3
  ring