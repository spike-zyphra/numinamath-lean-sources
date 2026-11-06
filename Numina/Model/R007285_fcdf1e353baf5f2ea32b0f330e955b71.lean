import Mathlib

theorem inequalities_221986 (x y : ℝ) : (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), sq_nonneg (x ^ 2 + y ^ 2), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - x * y), sq_nonneg (y ^ 2 - x * y), sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 3 + y ^ 3), sq_nonneg ((x - y) ^ 2), sq_nonneg (x * (x - y)), sq_nonneg (y * (x - y)), sq_nonneg ((x + y) ^ 2), sq_nonneg (x * y - x ^ 2), sq_nonneg (x * y - y ^ 2)]