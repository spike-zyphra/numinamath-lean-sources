import Mathlib

theorem algebra_10820 (n : ℝ) (hn : n = 7 / 9) : (round (n * 100) / 100 : ℝ) = 0.78 := by
  rw [hn]
  norm_num [round_eq]
  all_goals norm_num
  all_goals norm_num [round_eq]
  all_goals norm_num
  all_goals norm_num [round_eq]
  all_goals try { norm_num [round_eq] }
  all_goals norm_num