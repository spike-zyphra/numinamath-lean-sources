import Mathlib

theorem inequalities_50034 (x : ℝ) : x^12 - x^9 + x^4 - x + 1 > 0 := by
  nlinarith [sq_nonneg (x^6 - x^3 / 2), sq_nonneg (x^4 - x^2 / 2), sq_nonneg (x^2 - 1), sq_nonneg (x^3 - 1), sq_nonneg (x^3 + 1), sq_nonneg (x^4 - x^2), sq_nonneg (x^2 - x), sq_nonneg (x^2 + x), sq_nonneg (x^6 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1)]