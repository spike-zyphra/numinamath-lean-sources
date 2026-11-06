import Mathlib

theorem algebra_2483 (x : ℝ) (hx : x > 0) (h : (20 + x) * 0.2 = 20 * 0.15 + x) :
    x = 1.25 := by
  norm_num at h
  linarith