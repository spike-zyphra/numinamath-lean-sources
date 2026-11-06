import Mathlib

theorem algebra_193331 {x : ℝ} (hx : x > 0) (h : (1 + x / 100) * (1 + x / 100) = 2809 / 2500) :
    x = 6 := by
  nlinarith [h, sq_nonneg (1 + x / 100), sq_nonneg (53 / 50 : ℝ)]