import Mathlib

theorem algebra_292019 {x: ℕ} (hx: x = 7):
  (x - 4) ^ (x - 5) ^ (x - 6) ^ (x + 6) ^ (x + 5) = 9 := by 
  rw [hx]
  norm_num