import Mathlib

theorem number_theory_281902 : max (max (max (max (3/10 : ℚ) (9/20)) (12/25)) (27/50)) (49/100) = 27/50 := by
  norm_num [max_eq_right, max_eq_left]