import Mathlib

theorem number_theory_290972 (n : ℤ) :
    IsCoprime (2 * n + 1) (3 * n + 1) := by
  show IsCoprime (2 * n + 1) (3 * n + 1)
  use 3, -2
  ring