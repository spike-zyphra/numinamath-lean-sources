import Mathlib

theorem algebra_2764 {x : ℝ} (hx : x = -2) : (-x - abs x) / (x^2 + x) = 0 := by
  rw [hx]
  norm_num [abs_of_nonpos]
  all_goals norm_num
  all_goals norm_num