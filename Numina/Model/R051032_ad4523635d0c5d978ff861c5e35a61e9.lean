import Mathlib

theorem algebra_94969 {x y : ℝ} (hx : x = 0.7) (hy : y = 0.8) :
    (1 - x * y) * 100 = 44 := by 
  rw [hx, hy]
  norm_num