import Mathlib

theorem algebra_264745 {x : ℝ} (hx : x > 0) (h : 200 * x = 360 * (x - 32 / 100)) :
    360 * (x - 32 / 100) = 144 := by
  linarith