import Mathlib

theorem algebra_14598 : (5 : ℝ) ^ ((1 : ℝ) / 3) / 5 ^ ((1 : ℝ) / 5) = 5 ^ ((2 : ℝ) / 15) := by 
  have h1 : (5 : ℝ) ^ ((1 : ℝ) / 3) / (5 : ℝ) ^ ((1 : ℝ) / 5) = (5 : ℝ) ^ (((1 : ℝ) / 3) - (1 / 5)) := by
    rw [← Real.rpow_sub]
    all_goals norm_num
  rw [h1]
  have h2 : ((1 : ℝ) / 3) - (1 / 5) = (2 : ℝ) / 15 := by
    norm_num
  rw [h2]
  all_goals norm_num
  all_goals norm_num