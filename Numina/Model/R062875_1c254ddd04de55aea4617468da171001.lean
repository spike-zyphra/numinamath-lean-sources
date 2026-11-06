import Mathlib

theorem number_theory_249776 (x : ℝ) (hx : x < 50) (h : (x * 1.2) = 54) :
    x = 45 := by 
  norm_num at h 
  linarith