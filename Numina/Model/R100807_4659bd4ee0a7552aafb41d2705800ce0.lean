import Mathlib

theorem algebra_284855 (x y : ℤ) (hx : x = -4) (hy : y = 4) : -x * y > x / y ∧ -x * y > y - 1 ∧ -x * y > x - 1 ∧ -x * y > x + y := by 
  rw [hx, hy]
  norm_num