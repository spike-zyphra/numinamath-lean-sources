import Mathlib

theorem algebra_276325 (d t : ℝ) (ht : t > 0) (h1 : d / 20 = t + 4.5) (h2 : d / 10 = t + 5.25) :
    d / 12 = t + 5 := by 
  norm_num at h1 h2 ⊢
  linarith