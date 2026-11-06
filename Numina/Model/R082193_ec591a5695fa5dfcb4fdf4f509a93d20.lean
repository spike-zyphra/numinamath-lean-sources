import Mathlib

theorem algebra_114571 {x : ℝ} (hx : x > 0) (h : (1 + 25 / 100) * (1 - x / 100) = 1) :
    x = 20 := by
  nlinarith