import Mathlib

theorem algebra_15713 {x : ℝ} (hx : x = 200 / 0.4536) : round x = 441 := by 
  rw [hx]
  norm_num [round_eq]