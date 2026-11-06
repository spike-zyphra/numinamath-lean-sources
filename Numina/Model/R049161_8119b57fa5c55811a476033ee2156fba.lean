import Mathlib

theorem algebra_228580 (d : ℝ) (h : d > 0) (h1 : 2 * d = 3 / 8 * (d - 5.25)) :
    d = 21 := by
  norm_num at h1
  linarith