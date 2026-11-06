import Mathlib

theorem algebra_147501 (t : ℝ) (ht : t > 0) (h : 1.5 * t = 235 - 87 - 59 - 26) :
    t = 42 := by
  norm_num at h
  linarith