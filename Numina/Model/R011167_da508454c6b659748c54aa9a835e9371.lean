import Mathlib

theorem algebra_97379 (x : ℝ) (hx : x = -2016) : abs (abs (abs x - x) - abs x) - x = 4032 := by 
  rw [hx]
  norm_num [abs_of_nonneg, abs_of_nonpos]