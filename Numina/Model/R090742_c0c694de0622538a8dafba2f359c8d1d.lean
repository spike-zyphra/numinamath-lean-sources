import Mathlib

theorem algebra_167196 (d : ℝ) (h : d > 0) (h1 : 20 * d / 100 = 20 * 60) (h2 : 1600 / 30 = 20 * d / 100 - 1600 / 20) :
    d = 5200 := by
  norm_num at h1 h2 ⊢
  linarith