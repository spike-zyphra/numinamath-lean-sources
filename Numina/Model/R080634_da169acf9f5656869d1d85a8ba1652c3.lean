import Mathlib

theorem algebra_93823 : (10 : ℝ) ^ (Real.logb 10 7) = 7 := by
  rw [Real.rpow_logb]
  all_goals norm_num