import Mathlib

theorem algebra_21199 : round (4 / 7 * 10 : ℝ) / (10 : ℝ) = 0.6 := by 
  norm_num [round_eq]