import Mathlib

theorem algebra_609444 (p: ℝ) (h: 300 * p * 0.01 + 100 + 60 + 70 + 80 = 700 * 70 / 100): (p = 60) := by 
  norm_num at h
  linarith