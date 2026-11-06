import Mathlib


theorem algebra_311612 (a b x y : ℝ)
    (h1 : a * x + b * y = 3) (h2 : a * x ^ 2 + b * y ^ 2 = 7)
    (h3 : a * x ^ 3 + b * y ^ 3 = 16) (h4 : a * x ^ 4 + b * y ^ 4 = 42) : a * x ^ 5 + b * y ^ 5 = 20 := by 

  have eq1 : a * x^3 + b * y^3 = (x + y) * (a * x^2 + b * y^2) - x * y * (a * x + b * y) := by ring
  rw [h1, h2, h3] at eq1

  have eq2 : a * x^4 + b * y^4 = (x + y) * (a * x^3 + b * y^3) - x * y * (a * x^2 + b * y^2) := by ring
  rw [h2, h3, h4] at eq2 
  
  have eq3 : a * x^5 + b * y^5 = (x + y) * (a * x^4 + b * y^4) - x * y * (a * x^3 + b * y^3) := by ring
  rw [h4, h3] at eq3
  
  linarith only [eq1, eq2, eq3]
