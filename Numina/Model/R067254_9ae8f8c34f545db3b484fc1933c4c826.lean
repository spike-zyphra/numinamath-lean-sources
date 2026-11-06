import Mathlib

theorem algebra_674 (a b c : ℝ) (h : 140 + 80 + 60 = a * 100 + b * 10 + c)
    (h' : 140 + 80 + 60 + 10 = a * 100 + b * 10 + c + 234) :
    (c - 234) / 100 = 0.36 := by
  norm_num at h h' ⊢
  linarith