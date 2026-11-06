import Mathlib

theorem algebra_295076 (r : ℝ) (hr : r > 0) (h : 10 * r = 10 * (r + 40) + r) :
    10 * (r + 40) - 10 * r = 200 := by
  linarith