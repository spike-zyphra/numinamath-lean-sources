import Mathlib

theorem algebra_312762 {x : ℝ} (hx : 0 < x) (h : (1 + x / 100) * (1 - 5 / 6 * x) = 1) :
    x = 1 := by 
  nlinarith [sq_nonneg (x + 494 / 5), sq_nonneg (x)]