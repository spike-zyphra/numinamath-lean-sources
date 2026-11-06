import Mathlib

theorem algebra_19689 (a b c : ℝ) (h₀ : a - 7 * b + 8 * c = 4) (h₁ : 8 * a + 4 * b - c = 7) :
    a ^ 2 - b ^ 2 + c ^ 2 = 1 := by 
  have h2 : 12 * b - 13 * c = -5 := by 
    linarith [h₀, h₁]
  have hb : b = (13 * c - 5) / 12 := by linarith 
  have ha : a = (13 - 5 * c) / 12 := by 
    linarith [h₀, hb]
  rw [ha, hb]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - c), sq_nonneg (b - c)]