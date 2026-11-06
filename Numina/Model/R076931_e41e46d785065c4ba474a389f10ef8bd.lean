import Mathlib

theorem algebra_12533 : (30^3 + 40^3 + 50^3 : ℝ) ^ ((1 : ℝ) / 3) = 60 := by
  have h1 : (30^3 + 40^3 + 50^3 : ℝ) = (60 : ℝ) ^ (3 : ℝ) := by
    norm_num
  rw [h1]
  rw [← Real.rpow_mul]
  norm_num
  all_goals norm_num