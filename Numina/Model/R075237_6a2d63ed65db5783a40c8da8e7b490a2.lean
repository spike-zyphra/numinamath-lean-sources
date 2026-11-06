import Mathlib

theorem algebra_96793 : (1/4) ^ (-1/4 : ℝ) = Real.sqrt 2 := by
  have h1 : (1 / 4 : ℝ) ^ (-1 / 4 : ℝ) = (2 ^ (-2 : ℝ)) ^ (-1 / 4 : ℝ) := by norm_num
  rw [h1]
  have h2 : ((2 : ℝ) ^ (-2 : ℝ)) ^ (-1 / 4 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  rw [h2]
  have h3 : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow]
  rw [h3]
  all_goals norm_num