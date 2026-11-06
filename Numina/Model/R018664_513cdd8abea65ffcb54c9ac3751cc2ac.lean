import Mathlib

theorem algebra_205405 (x y : ℝ) (hx : x = 30) (hy : y = 10) :
    x * 1000 / y = 3000 := by
  rw [hx, hy]
  norm_num