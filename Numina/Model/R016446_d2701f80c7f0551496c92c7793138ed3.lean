import Mathlib

theorem inequalities_603529 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^3 + y^3 = x - y) : x^2 + 4 * y^2 < 1 := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1/2), mul_pos hx hy, sq_nonneg (x + y - 1), sq_nonneg (x - 2 * y), sq_nonneg (x + 2 * y), sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2), h]