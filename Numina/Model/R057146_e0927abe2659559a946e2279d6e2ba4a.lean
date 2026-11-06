import Mathlib

theorem algebra_15045 {x y : ℝ} (hx : x = (0 + (-4)) / 2) (hy : y = (7 + (-1)) / 2) :
    (x, y) = (-2, 3) := by
  rw [hx, hy]
  all_goals norm_num