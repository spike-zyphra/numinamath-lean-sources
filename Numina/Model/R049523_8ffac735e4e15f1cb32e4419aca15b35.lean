import Mathlib

theorem algebra_6493 (x y : ℚ) (hx : x = 3 / 5) (hy : y = 7 / 9) :
    (5 * x + 9 * y) / (45 * x * y) = 10 / 21 := by
  rw [hx, hy]
  norm_num