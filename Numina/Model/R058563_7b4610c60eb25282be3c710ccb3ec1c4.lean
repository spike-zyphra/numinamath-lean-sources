import Mathlib

theorem algebra_2242 (a b : ℝ) (h : a^2+b^2-2*a+b+10=0) : False:= by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b + 1 / 2), sq_nonneg (a - 1), sq_nonneg (b + 1 / 2)]