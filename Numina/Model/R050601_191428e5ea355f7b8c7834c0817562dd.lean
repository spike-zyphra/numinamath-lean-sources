import Mathlib

theorem inequalities_200097 (x y : ℝ) : x ^ 4 + y ^ 4 + 8 ≥ 8 * x * y := by
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - 2), sq_nonneg (x * y - 2), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x * y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 - 4), sq_nonneg (y ^ 2 - 4)]