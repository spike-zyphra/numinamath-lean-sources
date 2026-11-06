import Mathlib

theorem algebra_275060 (n : ℤ) (h : n^2 - (n+1)^2 = -199) :
    n^2 + (n+1)^2 = 19801 := by 
  have eq1 : n = 99 := by 
    nlinarith
  rw [eq1]
  norm_num