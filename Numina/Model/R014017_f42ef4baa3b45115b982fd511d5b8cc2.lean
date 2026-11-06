import Mathlib

theorem algebra_89 (m : ℝ) (hm : m > 0) (h : m ^ (2 / 3 : ℝ) = 4) : m = 8 := by
  have h1 : m = (m ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_mul]
    norm_num
    all_goals linarith
  rw [h] at h1
  have h2 : (4 : ℝ) ^ (3 / 2 : ℝ) = (8 : ℝ) := by
    have h4 : (4 : ℝ) ^ (3 / 2 : ℝ) = ((2 : ℝ) ^ (2 : ℝ)) ^ (3 / 2 : ℝ) := by
      norm_num
    rw [h4]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  rw [h2] at h1
  linarith