import Mathlib

theorem algebra_1674 (d : ℝ) (h : d > 0) (h1 : 2 * d / (2 + 1) = 3 * d / (3 + 1) + 36 / 60) :
    d = 36 := by
  norm_num at h1 
  linarith