import Mathlib

theorem algebra_264788 (x y z : ℤ) (h1 : x^2 + y - z = 10) (h2 : x^2 - y + z = 22) :
    x^2 + y^2 + z^2 ≥ 34 := by 
  have h3 : 2 * x^2 = 32 := by 
    linarith 
  have h4 : x^2 = 16 := by 
    linarith 
  have h5 : y = z - 6 := by 
    linarith 
  rw [h4, h5] 
  suffices (z - 3) ^ 2 ≥ 0 by 
    nlinarith 
  apply sq_nonneg