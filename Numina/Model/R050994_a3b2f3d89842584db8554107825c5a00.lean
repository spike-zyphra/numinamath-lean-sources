import Mathlib

theorem algebra_20070 {x : ℝ} (hx : x > 0) (h : (x - 2) * (5 - x) = 100) :
    (x - 4) * (5 - x) = 108 := by 
  nlinarith [sq_nonneg (x), sq_nonneg (x - 2), sq_nonneg (x - 5), sq_nonneg (x + 1)]