import Mathlib

theorem inequalities_1934 (a b : ℝ) (h₀ : 0 ≤ a) (h₁ : 0 ≤ b) (h₂ : a + b^2 ≥ a^2 + b^3) :
    3 * a^2 + 2 * b^3 ≤ 5 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1),
    mul_nonneg h₀ h₁, sq_nonneg (a - b), sq_nonneg ((a *  b) - 1), sq_nonneg (a -  b ^ 2), sq_nonneg (a ^ 2 - b ^ 3), sq_nonneg (a + b - 2)]