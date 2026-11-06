import Mathlib

theorem algebra_223093 (a b c d : ℝ) (h₀ : a ≥ b) (h₁ : b ≥ c) (h₂ : c ≥ d)
    (h₃ : a + b + c + d = 13) (h₄ : a^2 + b^2 + c^2 + d^2 = 43) : a * b ≥ 3 + c * d := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (a + b - c - d)]