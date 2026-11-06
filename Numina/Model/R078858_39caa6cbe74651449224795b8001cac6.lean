import Mathlib

theorem algebra_205217 {x : ℝ} (hx : x > 0) (h : 42 + x = 29 * (42 + x) / 20) :
    x = 48 := by
  linarith