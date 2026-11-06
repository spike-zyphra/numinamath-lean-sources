import Mathlib

theorem algebra_602303 (α : Real) (h : 7 * Real.sin α + 24 * Real.cos α = 25) : Real.tan α = 7 / 24 := by
  have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h2 : Real.sin α = (25 - 24 * Real.cos α) / 7 := by 
    linarith 
  have h3 : ( (25 - 24 * Real.cos α) / 7 ) ^ 2 + Real.cos α ^ 2 = 1 := by 
    rw [show Real.sin α = (25 - 24 * Real.cos α) / 7 by linarith [h2] ] at h1 
    linarith 
  have h4 : (25 - 24 * Real.cos α) ^ 2 + 49 * Real.cos α ^ 2 = 49 := by
    have h5 : ( (25 - 24 * Real.cos α) / 7 ) ^ 2 + Real.cos α ^ 2 = 1 := h3
    field_simp at h5 
    nlinarith 
  have h5 : 625 * Real.cos α ^ 2 - 1200 * Real.cos α + 576 = 0 := by
    nlinarith [h4]
  have h6 : Real.cos α = 24 / 25 := by
    nlinarith [h5]
  have h7 : Real.sin α = 7 / 25 := by 
    rw [h6] at h2 
    linarith 
  rw [Real.tan_eq_sin_div_cos, h7, h6]
  all_goals norm_num