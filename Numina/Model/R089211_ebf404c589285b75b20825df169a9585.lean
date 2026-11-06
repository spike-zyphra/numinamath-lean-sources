import Mathlib

theorem algebra_186292 (v : ℝ) (h : v > 0) (h1 : 60 * (1 + 1 / 4) = 75 * (1 + 3 / 60) + v * (1 + 1 / 4)) :
    v = 90 := by
  norm_num at h1 
  linarith