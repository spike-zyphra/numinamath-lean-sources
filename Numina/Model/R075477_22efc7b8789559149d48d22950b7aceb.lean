import Mathlib

theorem algebra_5884 (x : ℝ) (hx : x > 0) (h : (2000 - 1970) * 2 = (1970 - 2000) * x / 100) :
    x = 87.5 := by 
  norm_num at h 
  all_goals linarith