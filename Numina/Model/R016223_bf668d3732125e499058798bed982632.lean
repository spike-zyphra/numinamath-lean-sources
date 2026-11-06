import Mathlib

theorem algebra_279032 (x : ℤ) (h : 4 * x + 12 = 48) : x = 9 := by
  have eq1 : 4 * x = 36 := by 
    linarith 
  have eq2 : x = 9 := by 
    omega 
  exact eq2