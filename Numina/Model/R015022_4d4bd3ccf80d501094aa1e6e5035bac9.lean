import Mathlib

open Real

theorem algebra_3770 (walkbus walk total bus : ℝ) (hbus : bus = 37 / 48) (hwalkbus : walkbus = 37 - bus * 48) (hwalk : walk = walkbus / 4) (htotal : total = 1 * 60) (hsum : total = walk * 60 + bus * 60) : walk * 60 = 15 := by
  have h1 : walkbus = 0 := by
    rw [hwalkbus, hbus]
    norm_num
  have h2 : walk = 0 := by
    rw [hwalk, h1]
    norm_num
  rw [h2] at hsum
  rw [htotal] at hsum
  rw [hbus] at hsum
  norm_num at hsum
  all_goals linarith