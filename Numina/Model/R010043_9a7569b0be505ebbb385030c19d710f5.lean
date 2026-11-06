import Mathlib

theorem algebra_16498 {x y : ℝ} (hx : x = -20 / 100) (hy : y = 30 / 100) :
    (1 + x) * (1 + y) - 1 = 4 / 100 := by
  rw [hx, hy]
  norm_num