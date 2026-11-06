import Mathlib

theorem algebra_95186 (x : ℝ) (hx : x > 0) (h : (9 + x) * 30 / 100 = 9 * 50 / 100) :
    x = 6 := by
  linarith