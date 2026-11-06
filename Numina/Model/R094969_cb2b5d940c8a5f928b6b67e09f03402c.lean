import Mathlib

theorem inequalities_39921 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 = x - y) :
    x^2 + y^2 < 1 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y), sq_nonneg (x * y - y * y), 
          h, mul_pos hx hy, mul_pos hx hx, mul_pos hy hy]