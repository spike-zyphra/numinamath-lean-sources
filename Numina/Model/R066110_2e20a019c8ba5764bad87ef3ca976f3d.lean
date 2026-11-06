import Mathlib

theorem algebra_207716 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 3 + y ^ 3 = x - y) : x ^ 2 + y ^ 2 < 1 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x^2 - y^2), sq_nonneg (x*y), sq_pos_of_pos hx, sq_pos_of_pos hy, mul_pos hx hy]