import Mathlib

theorem algebra_318012 (l t : ℝ) (hl : l > 0) (ht : t > 0)
    (h1 : t / 3.6 = l / 10.8 + 22 / 3600) (h2 : t / 10.8 = l / 3.6 + 26 / 3600) :
    l = 286 := by
  norm_num at h1 h2 ⊢
  nlinarith