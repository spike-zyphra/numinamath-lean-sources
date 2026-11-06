import Mathlib

theorem algebra_12197 : round ((10^2000 + 10^2002 : ℝ) / (10^2001 + 10^2001 : ℝ)) = 5 := by
  norm_num [round_eq]