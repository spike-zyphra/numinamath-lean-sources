import Mathlib

theorem algebra_204461 (x : ℝ) (hx : x * 6 = 360.00) : x = 60 := by 
  norm_num at hx 
  linarith