import Mathlib

theorem algebra_21255 (t : ℝ) (ht : t ≥ 0) (h : -16*t^2 + 26*t + 105 = 0) :
    t = 3.5 := by
  nlinarith [sq_nonneg (t - 3.5), sq_nonneg (t * 16 ), sq_nonneg ((t - 3.5 ) * (t )  ), sq_nonneg (t - 0 ), sq_nonneg (t - 3.5) , sq_nonneg (t -7 / 2), sq_nonneg (t + 1.875 ) ]