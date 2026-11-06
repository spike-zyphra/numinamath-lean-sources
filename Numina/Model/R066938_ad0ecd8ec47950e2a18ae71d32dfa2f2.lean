import Mathlib

theorem number_theory_8019 (n : ℤ) : IsCoprime (21 * n + 4) (14 * n + 3) := by
  use -2, 3
  ring