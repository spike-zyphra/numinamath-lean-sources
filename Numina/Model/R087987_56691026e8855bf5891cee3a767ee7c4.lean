import Mathlib

theorem inequalities_180999 (x : ℝ) : x^4 - 12 * x^3 + 68 * x^2 - 192 * x + 207 ≥ 0 := by
  nlinarith [sq_nonneg (x ^ 2 - 6 * x + 23), sq_nonneg (x - 3), sq_nonneg (x - 3/2), sq_nonneg (x ^ 2 - 3 * x), sq_nonneg (x ^ 2 - 6 * x + 9), sq_nonneg (x * x - 3 * x)]