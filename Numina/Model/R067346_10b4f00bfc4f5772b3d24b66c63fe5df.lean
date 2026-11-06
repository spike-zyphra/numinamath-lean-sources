import Mathlib

theorem algebra_145736 (d : ℝ) (h : d > 0) (h1 : (d / (40 + 24)) = (43 / 18) * (d / (40 - 24))) (h2 : (d / (40 + 24)) + 1 = d / (40 - 24)) :
    d = 192 := by 
  norm_num at h1 h2
  linarith