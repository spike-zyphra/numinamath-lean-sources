import Mathlib

theorem algebra_415 (d : ℝ) (hd : d > 0) (h : d / 50 = d / 40 + 50 / (2 * (1.5 * 40) * (1 + 1 / 5 * 50))) :
    d = 9000 / 37 := by
  norm_num at h
  linarith