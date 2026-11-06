import Mathlib

theorem algebra_2429 (x y : ℤ) (hx : x = 6) (hy : y = 8) :
    x ^ 6 + y ^ 6 + 2 * x ^ 4 * y ^ 2 + 2 * x ^ 2 * y ^ 4 = 1020000 - 250400 := by
  rw [hx, hy]
  norm_num