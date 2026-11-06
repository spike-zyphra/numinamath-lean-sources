import Mathlib

theorem number_theory_102662 (n : ℤ) :
    IsCoprime (21 * n + 4) (14 * n + 3) := by
  show IsCoprime (21 * n + 4) (14 * n + 3)
  use -2, 3
  ring