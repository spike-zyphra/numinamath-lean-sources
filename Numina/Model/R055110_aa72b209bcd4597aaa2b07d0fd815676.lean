import Mathlib

theorem algebra_94824 : Real.logb 3 (27 * (9 ^ ((1 : ℝ) / 4)) * (9 ^ ((1 : ℝ) / 3))) = 4 + 1 / 6 := by
  have h1 : (27 : ℝ) = 3 ^ (3 : ℝ) := by norm_num
  have h2 : (9 : ℝ) = 3 ^ (2 : ℝ) := by norm_num
  have h3 : (9 : ℝ) ^ ((1 : ℝ) / 4) = 3 ^ (1 / 2 : ℝ) := by 
    rw [h2]
    rw [← Real.rpow_mul]
    ring_nf
    norm_num
    all_goals norm_num
  have h4 : (9 : ℝ) ^ ((1 : ℝ) / 3) = 3 ^ (2 / 3 : ℝ) := by 
    rw [h2]
    rw [← Real.rpow_mul]
    ring_nf
    norm_num
    all_goals norm_num
  have h5 : (27 : ℝ) * (9 ^ ((1 : ℝ) / 4)) * (9 ^ ((1 : ℝ) / 3)) = (3 : ℝ) ^ (25 / 6 : ℝ) := by
    rw [h1, h3, h4]
    rw [← Real.rpow_add, ← Real.rpow_add]
    norm_num
    all_goals norm_num
    all_goals norm_num
  rw [h5]
  rw [Real.logb_rpow]
  all_goals norm_num
  all_goals norm_num