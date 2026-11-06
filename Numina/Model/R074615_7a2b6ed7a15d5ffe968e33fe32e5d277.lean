import Mathlib

theorem calculus_60112 (d1 d2 v1 v2 : ℝ) (h1 : d1 = 3) (h2 : d2 = 4)
    (h3 : v1 = 4) (h4 : v2 = 3) :
    (d1 + d2) / (d1 / v1 + d2 / v2) = 3.36 := by 
  rw [h1, h2, h3, h4]
  norm_num