import Mathlib

theorem algebra_256190 (x : ℝ) (hx : x > 0) (h : 17 * x = 11 * (x - 5) + 17 / 3) :
    x = 5 := by
  linarith