import Mathlib

theorem number_theory_124323 (n : ℤ) :
    IsCoprime (39 * n + 4) (26 * n + 3) := by
  show IsCoprime (39 * n + 4) (26 * n + 3)
  use -2, 3
  ring