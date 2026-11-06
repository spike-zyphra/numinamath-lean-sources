import Mathlib

theorem algebra_193271 (x : ℝ) (hx : 0 < x) (h : (1 - 75 / 100) * (0.5 * 1000 - x) = (1 - 85 / 100) * 0.5 * 1000) :
    x = 200 := by
  norm_num at h
  linarith