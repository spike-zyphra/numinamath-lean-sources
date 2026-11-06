import Mathlib

theorem inequalities_600595 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 + y^3 ≥ x^3 + y^4) : x^2 + y^2 ≤ 2 := by
  nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1), sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1), mul_pos hx hy]