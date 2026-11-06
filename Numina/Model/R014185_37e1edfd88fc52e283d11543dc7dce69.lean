import Mathlib

theorem algebra_108294 (a b c d : ℝ) (h₀ : a + b + c + d = 20) (h₁ : a * b + a * c + a * d + b * c + b * d + c * d = 150) :
    a = 5 ∧ b = 5 ∧ c = 5 ∧ d = 5 := by 
  have h₂ : (a - 5) ^ 2 + (b - 5) ^ 2 + (c - 5) ^ 2 + (d - 5) ^ 2 = 0 := by 
    nlinarith
  have ha₁ : (a - 5) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5)]
  have ha₂ : a - 5 = 0 := by
    nlinarith [pow_two_nonneg (a - 5)]
  have ha : a = 5 := by
    linarith

  -- Similarly for b
  have hb₁ : (b - 5) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5)]
  have hb₂ : b - 5 = 0 := by
    nlinarith [pow_two_nonneg (b - 5)]
  have hb : b = 5 := by
    linarith
  
  -- Similarly for c
  have hc₁ : (c - 5) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5)]
  have hc₂ : c - 5 = 0 := by
    nlinarith [pow_two_nonneg (c - 5)]
  have hc : c = 5 := by
    linarith
  
  -- Similarly for d
  have hd₁ : (d - 5) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 5), sq_nonneg (b - 5), sq_nonneg (c - 5), sq_nonneg (d - 5)]
  have hd₂ : d - 5 = 0 := by
    nlinarith [pow_two_nonneg (d - 5)]
  have hd : d = 5 := by
    linarith
  
  exact ⟨ha, hb, hc, hd⟩