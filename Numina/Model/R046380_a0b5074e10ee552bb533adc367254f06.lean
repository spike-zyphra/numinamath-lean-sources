import Mathlib

theorem algebra_3189 {a b c d : ℝ} (h₀ : a + b + c + d = 20) (h₁ : a * b + a * c + a * d + b * c + b * d + c * d = 150) : a = b ∧ b = c ∧ c = d := by
  have h_eq : (a - 5) ^ 2 + (b - 5) ^ 2 + (c - 5) ^ 2 + (d - 5) ^ 2 = 0 := by
    nlinarith 
  have ha1 : a - 5 = 0 := by 
    nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5)]
  have hb1 : b - 5 = 0 := by 
    nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5)]
  have hc1 : c - 5 = 0 := by 
    nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5)]
  have hd1 : d - 5 = 0 := by 
    nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5)]
  have ha2 : a = 5 := by linarith
  have hb2 : b = 5 := by linarith
  have hc2 : c = 5 := by linarith
  have hd2 : d = 5 := by linarith
  constructor
  · -- Show a = b
    linarith
  constructor
  · -- Show b = c
    linarith 
  · -- Show c = d 
    linarith