import Mathlib

theorem algebra_16141 (n : ℝ) (h : 0 ≤ 5 + n) (h' : Real.sqrt (5 + n) = 7) :
    n = 44 := by 
  have h1 : (Real.sqrt (5 + n)) ^ 2 = 7 ^ 2 := by rw [h']
  rw [Real.sq_sqrt h] at h1
  norm_num at h1 
  linarith