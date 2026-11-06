import Mathlib

theorem algebra_318229 (x y : ℝ) (h : 2 * x ^ 2 + 3 * x * y + 2 * y ^ 2 = 1) :
    x + y + x * y ≥ -9 / 8 := by 
  nlinarith [sq_nonneg (2 * x - y), sq_nonneg (x - 2 * y), sq_nonneg (x + y + 1 / 4), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y + 1 / 4)]