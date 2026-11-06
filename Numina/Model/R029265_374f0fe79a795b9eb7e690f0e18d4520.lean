import Mathlib

theorem algebra_274587 {x : ℝ} (hx : x > 0) (h : (1 - 1 / 5) * x = 100 * (1 / 5) * x) :
    x = 79 := by
  linarith