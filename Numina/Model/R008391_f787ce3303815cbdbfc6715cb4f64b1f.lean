import Mathlib

theorem algebra_14837 : (round (9 / 13 * 10 : ℝ)) / (10 : ℝ) = 0.7 := by
  norm_num [round_eq]
  all_goals norm_num