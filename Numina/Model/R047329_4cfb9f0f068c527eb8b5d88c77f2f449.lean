import Mathlib

theorem algebra_207888 (α β : ℝ) (h₀ : Real.sin α + Real.sin β = 1) (h₁ : Real.cos α + Real.cos β = 0) :
    Real.cos (2 * α) + Real.cos (2 * β) = 1 := by 
  have h2 : Real.cos β = - Real.cos α := by 
    linarith 
  have h3 : Real.sin β = 1 - Real.sin α := by 
    linarith 
  have h4 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α 
  have h5 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β 
  rw [h3, h2] at h5 
  have h6 : Real.sin α = 1 / 2 := by 
    nlinarith 
  have h7 : Real.sin β = 1 / 2 := by 
    rw [h3] 
    linarith 
  have h8 : Real.cos (2 * α) = 1 - 2 * Real.sin α ^ 2 := by 
    rw [Real.cos_two_mul, Real.sin_sq]
    ring 
  have h9 : Real.cos (2 * β) = 1 - 2 * Real.sin β ^ 2 := by 
    rw [Real.cos_two_mul, Real.sin_sq]
    ring 
  rw [h8, h9] 
  rw [h6, h7] 
  norm_num