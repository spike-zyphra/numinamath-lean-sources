import Mathlib

open Real

theorem algebra_4327 {x : ℝ} (hx : x > 0) (h : 8 * 10 ^ 8 * x ^ (-3 / 2 : ℝ) = 800) :
    x ≥ 10000 := by
  have h1 : x ^ (-3 / 2 : ℝ) = 1 / 1000000 := by
    have h2 : x ^ (-3 / 2 : ℝ) = 800 / (8 * 10 ^ 8 : ℝ) := by
      have h3 : (8 * 10 ^ 8 : ℝ) * x ^ (-3 / 2 : ℝ) = (800 : ℝ) := by 
        linarith
      have h4 : x ^ (-3 / 2 : ℝ) = (800 / (8 * 10 ^ 8 : ℝ)) := by
        field_simp at h3 ⊢
        linarith
      linarith
    rw [h2]
    norm_num
  have h2 : x ≥ 10000 := by
    have h3 : x ^ (-3 / 2 : ℝ) = 1 / 1000000 := h1
    have h4 : x = (x ^ (-3 / 2 : ℝ)) ^ (-2 / 3 : ℝ) := by
      rw [← Real.rpow_mul]
      field_simp
      all_goals linarith
    rw [h4, h3]
    have h5 : (1 / (1000000 : ℝ) : ℝ) ^ (-2 / 3 : ℝ) = (10000 : ℝ) := by
      have h6 : (1 / (1000000 : ℝ) : ℝ) = (10 : ℝ) ^ (-6 : ℝ) := by norm_num
      rw [h6]
      rw [← Real.rpow_mul]
      norm_num
      norm_num
      all_goals norm_num
    rw [h5]
    all_goals linarith
  linarith