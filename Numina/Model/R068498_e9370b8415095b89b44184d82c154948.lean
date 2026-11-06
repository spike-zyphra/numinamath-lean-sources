import Mathlib

theorem algebra_13151 {x : ℤ} (h : 3 * x - 5 = 10 * x + 9) : 4 * (x + 7) = 20 := by
  have hx : x = -2 := by 
    linarith
  rw [hx]
  norm_num