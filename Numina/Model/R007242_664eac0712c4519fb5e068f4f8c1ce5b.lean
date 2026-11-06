import Mathlib

theorem algebra_13900 {x : ℝ} (hx : x ≠ 0)
    (h1 : (30 / 100) * x = (1 - 20 / 100) * x - 27) :
    x = 54 := by
  linarith