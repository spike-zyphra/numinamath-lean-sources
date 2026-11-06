import Mathlib

theorem algebra_20129 : (8^4 : ℝ) ^ ((1 : ℝ) / 12) = 2 := by
  have h1 : (8^4 : ℝ) = (2 : ℝ) ^ (12 : ℝ) := by norm_num
  rw [h1]
  rw [← Real.rpow_mul]
  norm_num
  all_goals norm_num