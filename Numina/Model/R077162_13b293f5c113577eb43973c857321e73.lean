import Mathlib

theorem algebra_243217 (α β : ℝ) (h₁ : Real.cos α + Real.cos β = 1 / 2) (h₂ : Real.sin α + Real.sin β = 1 / 4) :
    Real.cos (α - β) = -27 / 32 := by 
  have h3 : (Real.cos α + Real.cos β) ^ 2 = (1 / 2) ^ 2 := by 
    rw [h₁]
  
  have h4 : (Real.sin α + Real.sin β) ^ 2 = (1 / 4) ^ 2 := by 
    rw [h₂]
  
  have h5 : (Real.cos α + Real.cos β) ^ 2 + (Real.sin α + Real.sin β) ^ 2 = (1 / 4 : ℝ) + (1 / 16 : ℝ) := by
    rw [h3, h4]
    all_goals norm_num

  have h6 : (Real.cos α + Real.cos β) ^ 2 + (Real.sin α + Real.sin β) ^ 2 =
      (Real.cos α ^ 2 + Real.sin α ^ 2) + (Real.cos β ^ 2 + Real.sin β ^ 2) + 2 * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) := by
    ring
  have h7 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  have h8 : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
  
  rw [h6] at h5
  rw [h7, h8] at h5
  
  have h9 : Real.cos α * Real.cos β + Real.sin α * Real.sin β = -27 / 32 := by
    linarith
  
  have h10 : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := by 
    rw [Real.cos_sub]
  rw [h10]
  linarith [h9]