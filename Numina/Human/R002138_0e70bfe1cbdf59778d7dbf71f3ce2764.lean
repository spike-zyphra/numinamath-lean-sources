import Mathlib

open Real

theorem algebra_67882 : logb 3 (27 * 9 ^ ((1 : ℝ) / 4) * 9 ^ ((1 : ℝ) / 3)) = 4 + 1/6 := by
  have h2 : logb 3 (27 * 9 ^ ((1 : ℝ) / 4) * 9 ^ ((1 : ℝ) / 3)) = 3 + 1 / 2 + 2 / 3 := by
    have h21 : (27 : ℝ) = 3 ^ (3 : ℝ) := by norm_num
    have h22 : (9 : ℝ) ^ ((1 : ℝ) / 4) = 3 ^ (1 / 2 : ℝ) := by
      rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    have h23 : (9 : ℝ) ^ ((1 : ℝ) / 3) = 3 ^ (2 / 3 : ℝ) := by
      rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    rw [h21, h22, h23]
    rw [← Real.rpow_add, ← Real.rpow_add]
    rw [logb_rpow]
    all_goals norm_num
  rw [h2]
  norm_num