import Mathlib

theorem algebra_180772 (x y : ℝ) (h : x^3 + y^3 + 3 * x * y = 1) :
    x^2 + y^2 ≥ 1 / 2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (x * y - 1 / 4), sq_nonneg (x + y - 1), sq_nonneg (x - y), sq_nonneg (x + 1 / 2), sq_nonneg (y + 1 / 2)]