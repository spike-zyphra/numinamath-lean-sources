import Mathlib

theorem algebra_282324 (d : ℝ) (h : d > 0) (h1 : 7 * d / 2 = 8 * (d - 24) / 2) (h2 : 6.5 * d / 2 = 8 * (d - 20) / 2)
    (h3 : 7 * d / 2 = 6.5 * (d + 20) / 2) :
    d = 42 := by
  norm_num at h1 h2 h3
  linarith