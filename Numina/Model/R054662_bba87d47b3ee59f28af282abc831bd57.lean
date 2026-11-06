import Mathlib

theorem algebra_10786 (d : ℚ) (h : d = 1) :
    (1 - (1 - (1 / 3 : ℚ)) ^ 5) * d = 211 / 243 := by 
  rw [h]
  norm_num