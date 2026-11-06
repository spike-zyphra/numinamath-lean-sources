import Mathlib

theorem algebra_21225 (x : ℝ) (hx : x = 2) :
    x * (2 / 3)^3 = 16 / 27 := by
  rw [hx]
  norm_num