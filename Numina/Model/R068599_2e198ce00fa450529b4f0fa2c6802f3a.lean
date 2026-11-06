import Mathlib

theorem algebra_303077 {a b c : ℝ} (h₀ : a + 2 * b + 3 * c = 12) (h₁ : a^2 + b^2 + c^2 = a * b + b * c + c * a) :
    a + b^2 + c^3 = 14 := by 
  have h2 : (a - b)^2 + (b - c)^2 + (c - a)^2 = 0 := by 
    nlinarith 
  have hab : a - b = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hbc : b - c = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h3 : a = b := by linarith 
  have h4 : b = c := by linarith 
  have h5 : a = c := by linarith [h3, h4]
  have h6 : a = 2 := by 
    have h7 : a = b := h3 
    have h8 : b = c := h4 
    have h9 : a = c := by linarith [h7, h8] 
    linarith [h₀, h7, h8]
  have h7 : b = 2 := by linarith [h6, h3] 
  have h8 : c = 2 := by linarith [h7, h4] 
  rw [h6, h7, h8]
  norm_num