import Mathlib

theorem algebra_22135 (x y : ℝ) (hx : x = 3) (hy : y = 2) : 4 * x ^ 2 / (9 * y ^ 2) = 1 := by 
  rw [hx, hy]
  norm_num