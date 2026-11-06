import Mathlib

theorem algebra_93548 {x y : ℝ} (hx : x = 2) (hy : y = -2) :
    x - y^(x - y) = -14 := by
  rw [hx, hy]
  norm_num