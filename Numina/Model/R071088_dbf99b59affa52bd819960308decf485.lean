import Mathlib

theorem algebra_13681 {x y : ℝ} (hx : x ≠ 0) (h : 7 * x = 5 * y) :
    28 * x = 20 * y := by
  linarith [h]