import Mathlib

theorem number_theory_68266 (p : ℤ) :
    IsCoprime (21 * p + 4) (14 * p + 3) := by
  use -2, 3
  ring