import Mathlib

theorem algebra_98009 (x : ℝ) (hx : x = 10000) :
x * (1 - 36 / 100) * (1 - 4 / 100)- x * (1 - 40 / 100) = 144 := by
  rw [hx]
  norm_num