import Mathlib

theorem inequalities_7033 (a b : ℝ) : a ^ 2 + b ^ 2 ≥ a + b - 2 := by
  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (a + b - 1), sq_nonneg (a - b)]