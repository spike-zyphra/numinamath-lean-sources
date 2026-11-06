import Mathlib

theorem algebra_92936 {x y : ℝ} (hx : x = 80) (hy : y = 40) :
    (x * 0.4 + y * 0.55) / (x + y) = 0.45 := by
  rw [hx, hy]
  norm_num