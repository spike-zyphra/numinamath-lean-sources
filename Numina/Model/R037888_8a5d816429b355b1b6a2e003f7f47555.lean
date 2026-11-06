import Mathlib

theorem algebra_198376 {α : ℝ} (h : α ≠ 0) (x : ℝ) (hx : x = 2 + Real.sqrt 3)
    (h1 : x^2 - (Real.tan α + 1 / Real.tan α) * x + 1 = 0) :
    Real.sin α * Real.cos α = 1 / 4 := by
  have eq1 : (2 + Real.sqrt 3) ^ 2 - (Real.tan α + 1 / Real.tan α) * (2 + Real.sqrt 3) + 1 = 0 := by 
    rw [hx] at h1 
    linarith 
  have eq2 : Real.tan α ≠ 0 := by 
    by_contra h2
    have eq3 : Real.tan α = 0 := by linarith 
    rw [eq3] at eq1
    have h11 : (2 + Real.sqrt 3) ^ 2 + 1 = 0 := by 
      norm_num at eq1 ⊢ 
      all_goals linarith 
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have eq3 : Real.tan α + 1 / Real.tan α = 4 := by 
    have eq4 : (2 + Real.sqrt 3) ^ 2 - (Real.tan α + 1 / Real.tan α) * (2 + Real.sqrt 3) + 1 = 0 := eq1 
    have eq22 : Real.tan α ≠ 0 := eq2 
    field_simp [eq22] at eq4 ⊢ 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have eq4 : Real.sin α ≠ 0 := by 
    by_contra h2
    have h3 : Real.tan α = 0 := by 
      rw [Real.tan_eq_sin_div_cos]
      simp [h2] 
    rw [h3] at eq3 
    norm_num at eq3 
  have eq5 : Real.cos α ≠ 0 := by 
    by_contra h5
    have h6 : Real.tan α = 0 := by 
      rw [Real.tan_eq_sin_div_cos]
      simp [h5] 
    rw [h6] at eq3 
    norm_num at eq3 
  have eq6 : Real.tan α = Real.sin α / Real.cos α := by 
    rw [Real.tan_eq_sin_div_cos] 
  rw [eq6] at eq3 
  have eq12 : Real.sin α * Real.cos α = 1 / 4 := by
    have h13 : Real.sin α ≠ 0 := eq4 
    have h14 : Real.cos α ≠ 0 := eq5 
    have h33 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α 
    field_simp [h13, h14] at eq3 
    nlinarith [sq_pos_of_ne_zero (show Real.sin α ≠ 0 by exact h13), sq_pos_of_ne_zero (show Real.cos α ≠ 0 by exact h14), sq_nonneg (Real.sin α ^ 2 - Real.cos α ^ 2), sq_nonneg (Real.sin α * Real.cos α) ]
  linarith