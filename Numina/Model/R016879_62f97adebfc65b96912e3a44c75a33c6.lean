import Mathlib

theorem algebra_264957 {x y : ℕ} (hx : x = 1000) (hy : y = 100) :
    x ^ y = (10 ^ 100) ^ 3 := by
  rw [hx, hy]
  norm_num