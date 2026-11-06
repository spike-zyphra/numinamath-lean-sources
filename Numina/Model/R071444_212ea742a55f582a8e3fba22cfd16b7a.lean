import Mathlib

theorem algebra_157519 (t : ℝ) (ht : t > 0) (h : 100 * t = 100 * (t - 1) + 3 * t) :
    t = 33 + 1 / 3 := by
  linarith