import Mathlib

theorem algebra_10447 (d t1 t2 : ℝ) (h : d = 2) (h1 : t1 = 1/2) (h2 : t2 = 1/6) :
    d / (t1 + t2) = 3 := by
  rw [h, h1, h2]
  norm_num