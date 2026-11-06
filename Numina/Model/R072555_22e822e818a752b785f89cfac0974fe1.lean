import Mathlib

theorem algebra_243089 {x : ℝ} (hx : x > 0) (h : (1 / 2) * 30 + (1 / 2) * (30 + x) = 5) :
    x = 29 := by
  linarith