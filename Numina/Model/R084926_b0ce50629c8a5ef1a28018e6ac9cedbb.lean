import Mathlib

theorem algebra_299310 (x y : ℝ) (h : x ^ 2 + y ^ 2 + x * y = 1) :
    x + y ≤ 2 * √3 / 3 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2 * √3 / 3), Real.sqrt_nonneg 3, Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]