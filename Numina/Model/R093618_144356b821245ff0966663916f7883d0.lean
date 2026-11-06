import Mathlib

theorem algebra_8175 {n : ℤ} (h : (n - 2012) ^ 2 + (2016 - n) ^ 2 = 2014) :
    (2016 - n) * (n - 2012) = -999 := by
  have eq1 : (n - 2012) ^ 2 + (2016 - n) ^ 2 = 2014 := h
  have eq2 : (n - 2012) + (2016 - n) = 4 := by 
    linarith
  have eq3 : (n - 2012) ^ 2 + (2016 - n) ^ 2 = ((n - 2012) + (2016 - n)) ^ 2 - 2 * ((n - 2012) * (2016 - n)) := by
    ring
  rw [eq2] at eq3
  rw [eq1] at eq3
  linarith