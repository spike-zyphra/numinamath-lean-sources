import Mathlib

theorem algebra_317342 (a b c d : ℝ) (h₀ : a + b + c + d = 4) (h₁ : a * b + a * c + a * d + b * c + b * d + c * d = -14 / 3) :
    b + c + d ≤ 7 ∧ b + c + d ≥ -1 := by
  constructor
  · -- Show that b + c + d ≤ 7
    nlinarith [sq_nonneg (a + 3), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
      sq_nonneg (a - 5)]
  · -- Show that b + c + d ≥ -1
    nlinarith [sq_nonneg (a - 5), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
      sq_nonneg (a + 3)]