import Mathlib

theorem algebra_178 (x : ℝ) (hx : x = 4) : x ^ 2 - 8 ^ 2 / x ^ 2 = 12 := by
  rw [hx]
  norm_num