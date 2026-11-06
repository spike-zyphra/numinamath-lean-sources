import Mathlib

theorem algebra_176927 {x : ℝ} (hx : 0 < x) (h : (1 - 15 / 100) ^ 2 = (1 - x / 100) ^ 1) :
    x = 27.75 := by
  norm_num at h
  linarith