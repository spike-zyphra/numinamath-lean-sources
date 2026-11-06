import Mathlib

theorem number_theory_318744 : ∃ n : ℕ, n > 0 ∧ (29^n) % 1000 = 1 := by
  use 100
  constructor
  · -- Show n > 0
    norm_num
  · -- Show 29^n % 1000 = 1
    norm_num