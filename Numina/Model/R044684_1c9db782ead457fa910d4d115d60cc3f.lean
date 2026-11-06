import Mathlib

theorem algebra_21656 (x y : ℝ) (hx : x = 5) (hy : y = 4) :
    x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4 = 2101 := by
  rw [hx, hy]
  norm_num