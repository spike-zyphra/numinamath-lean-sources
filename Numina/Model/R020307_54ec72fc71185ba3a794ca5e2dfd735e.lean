import Mathlib

theorem algebra_11722 : (6 + 1 / 4 : ℝ) ^ ((1 : ℝ) / 2) = 5 / 2 := by
  have h1 : (6 + (1 : ℝ) / 4) = (25 / 4 : ℝ) := by
    norm_num
  rw [h1]
  have h2 : ((25 / 4 : ℝ) : ℝ) ^ ((1 : ℝ) / 2) = (5 / 2 : ℝ) := by
    rw [show (25 / 4 : ℝ) = (5 / 2) ^ 2 by norm_num]
    have h3 : ((5 / 2 : ℝ) ^ 2 : ℝ) ^ ((1 : ℝ) / 2) = (5 / 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    exact h3
  exact h2