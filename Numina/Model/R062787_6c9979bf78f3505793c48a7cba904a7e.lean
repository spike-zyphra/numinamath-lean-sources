import Mathlib

theorem algebra_2912 (d t1 t2 : ℝ) (h2 : t2 = d / 40) (h1 : t1 = d / 60) (h3 : t1 = t2 - 30 / 60) (ht : t2 ≠ 0) (hd : d > 0) : d = 60 := by 
  rw [h1, h2] at h3 
  linarith