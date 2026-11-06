import Mathlib

theorem algebra_96966 (v : ℝ) (h : v > 0) (h1 : 96 / 1.5 = (60 * 0.5 + 65 * 0.5 + v * 0.5) / (0.5 + 0.5 + 0.5)) :
v = 67 := by
  norm_num at h1 
  linarith