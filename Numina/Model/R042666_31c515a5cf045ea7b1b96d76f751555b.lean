import Mathlib


theorem algebra_13379 : ∃ x : ℝ, Real.rpow 2 x + 6 = 3 * Real.rpow 2 x - 26 := by
  use 4
  have h1 : Real.rpow 2 (4 : ℝ) = 16 := by
    norm_num [Real.rpow_natCast, pow_succ]
  rw [h1]
  norm_num