import Mathlib

theorem algebra_4520 (t : ℝ) (ht : t > 0) (h : (4800 - 100 * t) = 100 * t) :
    t = 24 := by
  linarith