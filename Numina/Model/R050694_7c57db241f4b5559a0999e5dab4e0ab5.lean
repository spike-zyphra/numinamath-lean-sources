import Mathlib

theorem algebra_216190 {x : ℝ} (hx : 0 < x) (h : (1 - x) * 0.95 + x * 0.98 = 1.5 / 100) :
    x = 1 / 2 := by
  norm_num at h
  linarith