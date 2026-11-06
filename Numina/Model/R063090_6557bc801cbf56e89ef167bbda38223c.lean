import Mathlib

theorem algebra_320408 (x y : ℝ) (h : 3*x^2+2*y^2=6*x) :
    x^2+y^2 ≤ 4 := by 
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y), sq_nonneg (x * (x - 2)), sq_nonneg (y ^ 2), sq_nonneg (3 * x - 2 * y), sq_nonneg (x + y), sq_nonneg (x + 2), sq_nonneg (x - 2)]