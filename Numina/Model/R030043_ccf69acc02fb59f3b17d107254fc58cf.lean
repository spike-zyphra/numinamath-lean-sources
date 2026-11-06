import Mathlib

theorem algebra_215168 (v : ℝ) (h : v > 0) (h1 : 90 * 1.2 = v * 1.2 + 90 * 8.5) (h2 : 90 * 2 = v * 2 + 90 * 9.5) :
    v = 30 := by
  norm_num at h1 h2
  linarith