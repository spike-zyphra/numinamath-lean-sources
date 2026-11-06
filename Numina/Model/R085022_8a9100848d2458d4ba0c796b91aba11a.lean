import Mathlib

theorem inequalities_126224 (x : ℝ) : 1 + x^2 + x^6 + x^8 ≥ 4 * x^4 := by
  nlinarith [sq_nonneg (x^4 - 2), sq_nonneg (x^2 - 1), sq_nonneg (x^2 + 1), sq_nonneg (x^4 - x^2), sq_nonneg (x^2 - x), sq_nonneg (x^2 + x), sq_nonneg (x^4 - 2*x^2), sq_nonneg (x^4 - 1), sq_nonneg (x^4 - x^6), sq_nonneg (x^2 - 1)]