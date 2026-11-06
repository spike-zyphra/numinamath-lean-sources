import Mathlib

theorem inequalities_111101 (a b : ℝ) : a^2 * (1 + b^4) + b^2 * (1 + a^4) ≤ (1 + a^4) * (1 + b^4) := by
  nlinarith [sq_nonneg (a^2 - a * b^2), sq_nonneg (b^2 - a * b^2), sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - a^2), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (a * b - 1)]