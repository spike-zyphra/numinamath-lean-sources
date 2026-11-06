import Mathlib

theorem algebra_15853 {r : ℝ} (hr : 2 * r - 1 > 0) (h : Real.logb 81 (2 * r - 1) = -1 / 2) :
    r = 5 / 9 := by
  have h1 : 2 * r - 1 = (81 : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [← h]
    field_simp [Real.rpow_logb, hr]
  have h2 : (81 : ℝ) ^ (-1 / 2 : ℝ) = (1 / 9 : ℝ) := by
    have h3 : (81 : ℝ) ^ (-1 / 2 : ℝ) = ((3 : ℝ) ^ (4 : ℝ)) ^ (-1 / 2 : ℝ) := by
      norm_num
    rw [h3]
    have h4 : ((3 : ℝ) ^ (4 : ℝ)) ^ (-1 / 2 : ℝ) = (3 : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith
    rw [h4]
    norm_num
  rw [h2] at h1
  have h3 : 2 * r - 1 = (1 / 9 : ℝ) := by
    linarith
  have h4 : 2 * r = (10 / 9 : ℝ) := by
    linarith
  linarith