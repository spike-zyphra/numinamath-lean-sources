import Mathlib

theorem algebra_275673 {x y : ℤ} (hx : x = 2 - 4 + 6) (hy : y = 1 - 3 + 5) : x - y = 1 := by 
  rw [hx, hy]
  norm_num