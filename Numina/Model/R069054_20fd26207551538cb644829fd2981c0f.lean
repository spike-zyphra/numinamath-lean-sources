import Mathlib

theorem algebra_21912 (x y : ℝ) (hx : x = (1 + (-7)) / 2) (hy : y = (1 + 5) / 2) :
    x * y = -9 := by
  rw [hx, hy]
  norm_num