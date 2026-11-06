import Mathlib

theorem algebra_97952 {H T : ℤ} (hH : H = 8 - (2 + 5)) (hT : T = 8 - 2 + 5) : H - T = -10 := by
  rw [hH, hT]
  all_goals norm_num