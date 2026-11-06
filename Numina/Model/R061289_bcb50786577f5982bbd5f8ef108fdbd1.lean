import Mathlib

theorem algebra_194739 (x : ℝ) (hx : x = 32) :
    x * (1 + 25 / 100) * (1 + 25 / 100) * (1 - 20 / 100) * (1 - 20 / 100) = 32 := by 
  rw [hx]
  norm_num