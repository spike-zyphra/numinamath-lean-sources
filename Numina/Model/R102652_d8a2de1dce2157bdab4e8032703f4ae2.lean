import Mathlib

theorem algebra_193932 (α : ℝ) : Real.sin α + Real.cos α ≠ 1.5 := by
  by_contra h
  have h1 : Real.sin α + Real.cos α = 1.5 := by 
    linarith
  have h2 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h3 : (Real.sin α + Real.cos α) ^ 2 = (1.5 : ℝ) ^ 2 := by 
    rw [h1]
  have h4 : (Real.sin α + Real.cos α) ^ 2 = Real.sin α ^ 2 + Real.cos α ^ 2 + 2 * (Real.sin α * Real.cos α) := by 
    ring
  have h5 : Real.sin α ^ 2 + Real.cos α ^ 2 + 2 * (Real.sin α * Real.cos α) = (1.5 : ℝ) ^ 2 := by 
    linarith [h3, h4]
  rw [h2] at h5
  have h6 : Real.sin α * Real.cos α = (0.625 : ℝ) := by
    nlinarith
  have h7 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by 
    rw [Real.sin_two_mul]
  have h8 : Real.sin (2 * α) = 1.25 := by
    nlinarith [h6, h7]
  have h9 : Real.sin (2 * α) ≤ 1 := by
    apply Real.sin_le_one
  linarith [h8, h9]