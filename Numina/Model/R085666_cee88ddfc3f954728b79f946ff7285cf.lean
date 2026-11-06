import Mathlib

theorem algebra_275732 (d : ℝ) (h : d > 0) (h1 : 3.3 * (d / 3.3 - 24 / 60) = 3 * (d / 3.3 - 36 / 60) + 14) (h2 : 3.3 * (d / 3.3 - 36 / 60) = 3 * (d / 3.3 - 24 / 60) + 9) :
    d = 660 := by
  norm_num at h1 h2
  linarith