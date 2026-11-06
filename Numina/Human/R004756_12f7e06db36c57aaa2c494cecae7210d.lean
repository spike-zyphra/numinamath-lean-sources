import Mathlib

theorem algebra_317524 {a b c : ℝ} (h₀ : b + c = 8) (h₁ : b * c = a ^ 2 - 12 * a + 52) :
    a + b + c = 14 := by
  have h2 : a = 6 := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (a - 6)]
  linarith [h₀, h2]