import Mathlib

theorem algebra_95990 (x : ℝ) (hx : x = 1 / 3) :
    (1 - x) * (1 - x) = 4 / 9 := by 
  rw [hx]
  norm_num