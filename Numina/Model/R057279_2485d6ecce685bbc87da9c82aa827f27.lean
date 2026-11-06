import Mathlib

theorem algebra_270155 (x : ℝ) (hx : x > 0) (h : (21 - x) * 18 / 100 + x * 90 / 100 = 21 * 42 / 100) :
    x = 7 := by
  linarith