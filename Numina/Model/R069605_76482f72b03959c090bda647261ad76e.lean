import Mathlib

theorem algebra_599373 (α : ℝ) (h : Real.cos α + 2 * Real.sin α = -Real.sqrt 5) : Real.tan α = 2 := by
  have h1 : Real.cos α = -Real.sqrt 5 - 2 * Real.sin α := by linarith [h]

  have h2 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α

  have h3 : Real.sin α = -2 * Real.sqrt 5 / 5 := by
    rw [h1] at h2
    have h5 : Real.sqrt 5 > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sin α + 2 * Real.sqrt 5 / 5), sq_nonneg (Real.sqrt 5 ^ 2 - 5)]
  
  have h4 : Real.cos α = -Real.sqrt 5 / 5 := by
    rw [h3] at h1
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]

  have h5 : Real.tan α = Real.sin α / Real.cos α := by
    rw [Real.tan_eq_sin_div_cos]

  rw [h5]
  rw [h3, h4]
  field_simp [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]