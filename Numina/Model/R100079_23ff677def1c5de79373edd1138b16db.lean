import Mathlib

theorem inequalities_221380 (x y : ℝ) (h : x^12 + y^12 ≤ 2) :
    x^2 + y^2 + x^2 * y^2 ≤ 3 := by
  nlinarith [sq_nonneg (x ^ 4 - 1), sq_nonneg (y ^ 4 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1),
    sq_nonneg (x * y), sq_nonneg (x ^ 2 * y ^ 2 - 1),
    sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 4 - y ^ 4), sq_nonneg (x ^ 6 - y ^ 6),
    sq_nonneg (x ^ 8 - y ^ 8), sq_nonneg (x ^ 10 - y ^ 10), sq_nonneg (x ^ 12 - y ^ 12)]