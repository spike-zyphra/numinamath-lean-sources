import Mathlib

theorem algebra_10781 {y : ℝ} (h : (6 + 9 + 18) / 3 = (12 + y) / 2) : y = 10 := by
  norm_num at h
  linarith