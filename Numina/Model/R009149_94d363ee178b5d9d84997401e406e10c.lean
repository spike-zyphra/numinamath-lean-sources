import Mathlib

theorem algebra_57209 {x : ℝ} (hx : x ≠ 0) (h : (1 - 88 / 100) * 6000 = (1 - 82 / 100) * x) :
    x = 4000 := by 
  norm_num at h 
  linarith