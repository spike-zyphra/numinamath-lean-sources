import Mathlib

theorem number_theory_162079 (n : ℤ) :
    IsCoprime (14 * n + 3) (21 * n + 4) := by
  use 3, -2
  ring