import Mathlib

theorem number_theory_211369 :
    ∃ x y z, x > 1 ∧ y > 1 ∧ z > 1 ∧ x * y * z = 2 ^ 58 + 1 := by
  use 5, 107367629, 536903681
  norm_num