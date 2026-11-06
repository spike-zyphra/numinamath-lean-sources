import Mathlib

theorem algebra_47550 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^3 + y^3 + (x + y)^3 + 30 * x * y = 2000) : x + y = 10 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 10), sq_nonneg (x * y - 10 * (x + y)), sq_nonneg (x * y), sq_nonneg (x + y), sq_nonneg (x * y - 10 * x - 10 * y), sq_nonneg (x^2 + y^2 - 100),
    mul_pos hx hy]