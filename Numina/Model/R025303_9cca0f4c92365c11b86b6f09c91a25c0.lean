import Mathlib

theorem inequalities_65883 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^3 + y^3 = x - y) : x^2 + 4 * y^2 < 1 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x^2 - y^2), sq_nonneg (x^3 - y^3),
          sq_nonneg (x - 2 * y), sq_nonneg (2 * y - x), sq_nonneg (x + y - 1),
          sq_nonneg (x * y - 1/4), mul_pos hx hy, mul_pos hx hx, mul_pos hy hy]