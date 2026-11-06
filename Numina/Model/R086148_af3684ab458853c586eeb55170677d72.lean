import Mathlib

theorem algebra_123074 (a b c d e : ℝ) (h₀ : a + b + c + d + e = 8) (h₁ : a^2 + b^2 + c^2 + d^2 + e^2 = 16) :
    e ≤ 16 / 5 := by
  have h2 : a + b + c + d = 8 - e := by linarith 
  have h3 : a^2 + b^2 + c^2 + d^2 ≥ (a + b + c + d) ^ 2 / 4 := by 
    nlinarith [sq_nonneg (a + b + c + d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  have h4 : a^2 + b^2 + c^2 + d^2 ≥ (8 - e) ^ 2 / 4 := by
    nlinarith [h2, h3]
  nlinarith [h₁, h4]