import Mathlib

theorem algebra_179127 (α : ℝ) (h : Real.tan α = -1 / 2) :
    (Real.sin (2 * α) + 2 * Real.cos (2 * α)) / (4 * Real.cos (2 * α) - 4 * Real.sin (2 * α)) = 1 / 14 := by
  have h1 : Real.cos α ≠ 0 := by 
    by_contra h1
    have htan : Real.tan α = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h1]
    rw [htan] at h 
    linarith
  have h2 : Real.sin α = -1 / 2 * Real.cos α := by 
    have htan : Real.tan α = Real.sin α / Real.cos α := by 
      rw [Real.tan_eq_sin_div_cos]
    rw [htan] at h
    have hne : Real.cos α ≠ 0 := h1
    field_simp [hne] at h ⊢ 
    linarith
  have h3 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h4 : (-1 / 2 * Real.cos α) ^ 2 + Real.cos α ^ 2 = 1 := by 
    rw [show Real.sin α = -1 / 2 * Real.cos α by linarith [h2] ] at h3
    linarith
  have h5 : Real.cos α ^ 2 = 4 / 5 := by 
    nlinarith
  have h6 : Real.sin α ^ 2 = 1 / 5 := by 
    have : Real.sin α = -1 / 2 * Real.cos α := h2
    rw [this]
    nlinarith
  have h7 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by 
    rw [Real.sin_two_mul]
  have h8 : Real.sin (2 * α) = - Real.cos α ^ 2 := by 
    rw [h7, h2]
    ring
  have h9 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by 
    rw [Real.cos_two_mul]
  have h10 : Real.cos (2 * α) = 3 / 5 := by 
    rw [h9]
    have h5' : Real.cos α ^ 2 = 4 / 5 := h5 
    nlinarith 
  have h11 : Real.sin (2 * α) = -4 / 5 := by 
    rw [h8] 
    have h5' : Real.cos α ^ 2 = 4 / 5 := h5 
    linarith 
  have h12 : Real.sin (2 * α) + 2 * Real.cos (2 * α) = 2 / 5 := by 
    rw [h11, h10]
    linarith 
  have h13 : 4 * Real.cos (2 * α) - 4 * Real.sin (2 * α) = 28 / 5 := by 
    rw [h10, h11]
    linarith 
  rw [h12, h13]
  all_goals norm_num