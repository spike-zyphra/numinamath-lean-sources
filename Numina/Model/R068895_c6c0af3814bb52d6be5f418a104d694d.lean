import Mathlib

theorem algebra_10617 : (64 : ℝ) ^ ((1 : ℝ) / 2) * (27 ^ ((-1 : ℝ) / 3)) * (16 ^ ((1 : ℝ) / 4)) = 16 / 3 := by
  have h1 : (64 : ℝ) ^ ((1 : ℝ) / 2) = 8 := by
    have h1 : (64 : ℝ) = 8 ^ (2 : ℝ) := by norm_num
    rw [h1]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  have h2 : (27 : ℝ) ^ ((-1 : ℝ) / 3) = 1 / 3 := by
    have h21 : (27 : ℝ) = 3 ^ (3 : ℝ) := by norm_num
    rw [h21]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  have h3 : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
    have h31 : (16 : ℝ) = 2 ^ (4 : ℝ) := by norm_num
    rw [h31]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  rw [h1, h2, h3]
  norm_num