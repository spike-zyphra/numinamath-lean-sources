import Mathlib

theorem algebra_216645 (d : ℝ) (h : d > 0) (h1 : 3 * (d / 3 - 10 / 60) ≤ 1.5 * (d / 3 - 10 / 60) + 1.5 * (d / 3 - 10 / 60) / 2) :
    d ≤ 1.375 := by
  norm_num at h1
  linarith