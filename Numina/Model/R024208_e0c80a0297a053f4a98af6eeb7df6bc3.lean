import Mathlib

theorem algebra_11310 {k : ℝ} (h : k ≠ 0) (h1 : (3 * Real.sqrt 2) = k * (81 : ℝ) ^ ((1 : ℝ) / 4)) :
    (2) = k * (4 : ℝ) ^ ((1 : ℝ) / 4) := by
  have h2 : (81 : ℝ) ^ ((1 : ℝ) / 4) = 3 := by
    rw [show (81 : ℝ) = 3 ^ (4 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  have hk : k = Real.sqrt 2 := by
    rw [h2] at h1
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h3 : (4 : ℝ) ^ ((1 : ℝ) / 4) = Real.sqrt 2 := by
    have h4 : (4 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    rw [h4]
    rw [← Real.sqrt_eq_rpow]
  rw [h3, hk]
  have h5 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    calc
      Real.sqrt 2 * Real.sqrt 2 = (Real.sqrt 2) ^ 2 := by ring
      _ = 2 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
  linarith [h5]