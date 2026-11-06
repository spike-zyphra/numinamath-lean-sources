import Mathlib

theorem algebra_50562 (x : ℝ) (hx : x > 0) (h : x * 0.15 + (250 - x) * 0.35 = 250 * 0.21) :
    x = 175 := by 
  norm_num at h 
  linarith