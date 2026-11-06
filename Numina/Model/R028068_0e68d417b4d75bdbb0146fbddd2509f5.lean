import Mathlib

theorem algebra_95077 {x y : ℝ} (hx : x = 8 / 3) (hy : y = 8 / 2) :
    (x + y) * 40 / 100 = x := by
  rw [hx] at *
  rw [hy] at *
  norm_num
  all_goals norm_num