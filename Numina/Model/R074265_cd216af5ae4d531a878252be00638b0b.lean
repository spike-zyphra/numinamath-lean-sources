import Mathlib

theorem algebra_283946 (a b c : ℝ) (h₀ : a = 8 - b) (h₁ : c^2 = a * b - 16) : a + c = 4 := by
  rw [h₀] at h₁ 
  have h2 : c^2 = -(b - 4)^2 := by 
    nlinarith 
  have h3 : c^2 ≥ 0 := by 
    exact sq_nonneg c 
  have h4 : (b - 4)^2 ≤ 0 := by 
    nlinarith [sq_nonneg (b - 4), h2] 
  have h6 : (b - 4)^2 = 0 := by 
    nlinarith [sq_nonneg (b - 4), h4] 
  have h7 : b - 4 = 0 := by 
    nlinarith [sq_nonneg (b - 4), h6] 
  have h8 : b = 4 := by 
    linarith 
  have h9 : a = 4 := by 
    rw [h8] at h₀ 
    linarith 
  have h10 : c = 0 := by 
    nlinarith [sq_nonneg c, h2, h6] 
  linarith [h9, h10]