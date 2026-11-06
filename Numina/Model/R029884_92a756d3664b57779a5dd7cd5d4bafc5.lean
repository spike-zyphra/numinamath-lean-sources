import Mathlib

theorem algebra_108314 {α β : ℝ} (h₁ : α > 0) (h₂ : β > 0)
    (h₃ : Real.logb 3 α + α - 3 = 0) (h₄ : 3^β + β - 3 = 0) :
    α + β = 3 := by
  have h5 : Real.logb 3 α = 3 - α := by linarith 
  have h6 : α = (3 : ℝ) ^ (3 - α : ℝ) := by 
    have h7 : Real.logb 3 α = 3 - α := h5
    rw [←h7]
    field_simp [Real.rpow_logb, show (3 : ℝ) > 1 by norm_num, show (3 : ℝ) > 0 by norm_num, show (α : ℝ) > 0 by linarith]
  
  by_cases h : β < 3 - α
  · -- Case 1: Assume β < 3 - α.
    have h8 : (3 : ℝ) ^ β < (3 : ℝ) ^ (3 - α : ℝ) := by 
      apply Real.rpow_lt_rpow_of_exponent_lt 
      all_goals linarith 
    have h9 : (3 : ℝ) ^ β = 3 - β := by linarith 
    have h10 : (3 : ℝ) ^ (3 - α : ℝ) = α := by linarith [h6] 
    nlinarith 
  by_cases h7 : β > 3 - α 
  · -- Case 2: Assume β > 3 - α.
    have h8 : (3 : ℝ) ^ β > (3 : ℝ) ^ (3 - α : ℝ) := by 
      apply Real.rpow_lt_rpow_of_exponent_lt 
      all_goals linarith 
    have h9 : (3 : ℝ) ^ β = 3 - β := by linarith 
    have h10 : (3 : ℝ) ^ (3 - α : ℝ) = α := by linarith [h6] 
    nlinarith 
  · -- Case 3: Assume β = 3 - α.
    have h8 : β = 3 - α := by linarith 
    linarith