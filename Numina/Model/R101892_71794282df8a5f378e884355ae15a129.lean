import Mathlib

theorem algebra_209912 (x y : ℝ) (h : 2*x^2-6*x+y^2=0) :
    x^2+y^2+2*x ≤ 15 := by
  nlinarith [sq_nonneg (x - 3), sq_nonneg (y), sq_nonneg (x - 0), sq_nonneg (x - 3)]