import Mathlib

theorem algebra_70863 (x : ℝ) (hx : x = 100) :
    (x * 1.1) * 0.9 = 99 := by
  rw [hx]
  norm_num
  all_goals tauto