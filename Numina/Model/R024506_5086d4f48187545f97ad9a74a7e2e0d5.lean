import Mathlib

theorem algebra_140392 {a b c d : ℝ} (h₀ : a^2 + b^2 = 1) (h₁ : c^2 + d^2 = 1) (h₂ : a * c + b * d = 0) :
    a * b + c * d = 0 := by
  nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a + d), sq_nonneg (b + c)]