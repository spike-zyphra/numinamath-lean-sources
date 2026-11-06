import Mathlib

theorem algebra_1209 {x : ℝ} (hx : 60 - 60 * 0.2 = x + x / 3) : x = 36 := by
  norm_num at hx 
  linarith