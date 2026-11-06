import Mathlib

theorem algebra_193877 {x : ℝ} (hx : 0 < x) (h : (12 + x) * 0.4 = 12 * 0.45) :
    x = 1.5 := by
  norm_num at h
  linarith