import Mathlib

theorem algebra_19892 (t : ℝ) (ht : -16*t^2-60*t+54=0) (htpos : 0 < t) :
    t=0.75 := by
  nlinarith [sq_nonneg (t - 0.75), sq_nonneg (t + 4.5)]