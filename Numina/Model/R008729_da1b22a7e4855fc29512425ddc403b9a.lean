import Mathlib

theorem algebra_21088 (c : ℝ) (hc : c = 1483) : round (((c / 75) / 52) * 10 ^ 2) = 38 := by
  rw [hc]
  norm_num [round_eq]
  all_goals norm_num