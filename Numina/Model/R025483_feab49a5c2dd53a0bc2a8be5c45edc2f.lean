import Mathlib

theorem algebra_254781 (a b c d : ℝ) (h₀ : a^2 + b^2 = c^2 + d^2) (h₁ : a * b + c * d > 0)
    (h₂ : a * c + b * d > 0) : a * d + b * c > 0 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a - c), sq_nonneg (b - d), 
          sq_nonneg (a + d - (b + c)), sq_nonneg (a + b - (c + d)), 
          sq_nonneg (a * b - c * d), sq_nonneg (a * c - b * d)]