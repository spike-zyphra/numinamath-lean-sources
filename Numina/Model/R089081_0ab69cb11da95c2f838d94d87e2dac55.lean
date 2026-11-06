import Mathlib

theorem inequalities_4116 (a b : ℝ)
  (h : a^2 + b^2 ≤ 2) : a * b + 3 ≥ 2 * a + 2 * b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg (a - 1), sq_nonneg (b - 1)]