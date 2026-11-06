import Mathlib

theorem algebra_140672 {x : ℝ} (hx : x > 0) (h : 30 * 12000 + 15 / 100 * x = 60900) :
    x ≥ 1321412 := by
  linarith