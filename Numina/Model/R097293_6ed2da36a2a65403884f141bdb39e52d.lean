import Mathlib

theorem algebra_599956 (α : ℝ) (h : Real.cos α + 2 * Real.sin α = -Real.sqrt 5) :
    Real.tan α = 2 := by
  have h1 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  have h2 : Real.cos α = -Real.sqrt 5 - 2 * Real.sin α := by linarith
  rw [h2] at h1
  have h3 : 5 * Real.sin α ^ 2 + 4 * Real.sqrt 5 * Real.sin α + 4 = 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h4 : Real.sin α = -2 * Real.sqrt 5 / 5 := by
    nlinarith [sq_nonneg (Real.sin α * 5 + 2 * Real.sqrt 5), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h5 : Real.cos α = -Real.sqrt 5 / 5 := by
    rw [h4] at h2
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  rw [Real.tan_eq_sin_div_cos]
  rw [h4, h5]
  field_simp [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), show Real.sqrt 5 ≠ 0 by positivity]
  <;> nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  <;> try { tauto }