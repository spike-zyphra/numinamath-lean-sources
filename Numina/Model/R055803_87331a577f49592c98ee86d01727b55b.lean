import Mathlib

theorem inequalities_219880 (x y : ℝ) (h : 2 * x + 4 * y = 1) : x ^ 2 + y ^ 2 ≥ 1 / 20 := by
  nlinarith [sq_nonneg (2 * x - 1 / 10), sq_nonneg (2 * y - 1 / 5), sq_nonneg (x - 1 / 10), sq_nonneg (y - 1 / 5), sq_nonneg (2 * x + 4 * y - 1)]