import Mathlib

theorem inequalities_37072 (x y : ℝ)
    (h : x ^ 4 * y ^ 2 + y ^ 4 + 2 * x ^ 3 * y + 6 * x ^ 2 * y + x ^ 2 + 8 ≤ 0) :
    x ≥ -1 / 6 := by 
  nlinarith [sq_nonneg (x ^ 2 * y + x + 3), sq_nonneg (y ^ 2 - x ^ 2), sq_nonneg (y + 3), sq_nonneg (x + 1 / 6), sq_nonneg (y + x), sq_nonneg (x + 2), sq_nonneg (x * y + 3), sq_nonneg (y - 2), sq_nonneg (x + 1)]