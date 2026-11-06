import Mathlib

theorem algebra_170705 (d : ℝ) (h : d > 0) (t1 t2 : ℝ)
    (ht1 : t1 = d / (6 + 4)) (ht2 : t2 = d / (6 - 4)) (ht : t2 = t1 - 10) :
    t1 = 30 := by
  norm_num at ht1 ht2 
  nlinarith