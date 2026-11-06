import Mathlib

theorem algebra_1077 {a b c : ℝ} (h₀ : a^2 - 6 * b = -14) (h₁ : b^2 - 8 * c = -23) (h₂ : c^2 - 4 * a = 8) : a + b + c = 9 := by
  nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 3), sq_nonneg (c - 4)]