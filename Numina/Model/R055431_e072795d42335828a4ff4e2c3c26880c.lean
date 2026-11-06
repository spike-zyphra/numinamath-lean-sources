import Mathlib

theorem algebra_652 (d t : ℝ) (h : 0 < d) (h1 : 0 < t) (h2 : d / (28 + 4) = t + d / (20 + 4)) (h3 : d / (20 + 4) = t + 40 / (28 + 4)) : d = 240 := by
  norm_num at h2 h3
  linarith