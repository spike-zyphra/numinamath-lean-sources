import Mathlib

theorem algebra_154775 (x y : ℝ) (h : ((x - 4)^2 / 4) + (y^2 / 9) = 1) :
    (x^2 / 4) + (y^2 / 9) ≤ 9 := by
  nlinarith [sq_nonneg (x - 6), sq_nonneg (y ^ 2 / 9 - 0), sq_nonneg (x - 4), sq_nonneg (y), sq_nonneg (x - 6 * (x - 4) / 4), sq_nonneg (y - 0), sq_nonneg (x - 2), sq_nonneg (x - 6), sq_nonneg (y ^ 2), sq_nonneg ((x - 4) ^ 2), sq_nonneg ((x - 4) * y)]