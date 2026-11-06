import Mathlib

theorem algebra_18936 {x y : ℝ} (hx : x = 8.5) (hy : y = 11) :
    max (x / 2) (y / 2) = 5.5 := by
  rw [hx, hy]
  norm_num
  all_goals norm_num