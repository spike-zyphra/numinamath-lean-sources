import Mathlib

theorem number_theory_12481 (x : ℚ) (hx : x.den > 0) (h : x = 3 / 9) :
    x.den = 3 := by 
  rw [h]
  norm_num