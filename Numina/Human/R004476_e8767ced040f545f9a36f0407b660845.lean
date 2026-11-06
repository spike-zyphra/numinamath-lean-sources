import Mathlib

theorem algebra_272387 (x : ℝ) (hx : x = 1 / 2) : x > x ^ 2 := by 
  rw [hx]
  norm_num