import Mathlib

theorem algebra_326544 (a b x y : ℝ)
    (h1 : a * x + b * y = 3)
    (h2 : a * x^2 + b * y^2 = 7)
    (h3 : a * x^3 + b * y^3 = 16)
    (h4 : a * x^4 + b * y^4 = 42) :
    a * x^5 + b * y^5 = 20 := by

  have eq1 : a * x^2 + b * y^2 = (x + y) * (a * x + b * y) - x * y * (a + b) := by
    ring_nf

  rw [h1] at eq1
  have eq5 : (x + y) * 3 - x * y * (a + b) = 7 := by linarith [h2, eq1]

  have eq2 : a * x^3 + b * y^3 = (x + y) * (a * x^2 + b * y^2) - x * y * (a * x + b * y) := by 
    ring_nf

  rw [h2, h1] at eq2
  have eq6 : (x + y) * 7 - x * y * 3 = 16 := by linarith [h3, eq2]

  have eq3 : a * x^4 + b * y^4 = (x + y) * (a * x^3 + b * y^3) - x * y * (a * x^2 + b * y^2) := by 
    ring_nf

  rw [h3, h2] at eq3
  have eq7 : (x + y) * 16 - x * y * 7 = 42 := by linarith [h4, eq3]

  have h5 : x + y = -14 := by
    nlinarith [sq_nonneg (x * y), sq_nonneg (a + b), sq_nonneg (a * x - b * y), sq_nonneg (a - b), sq_nonneg (x - y)]

  have h6 : x * y = -38 := by
    rw [show x + y = -14 by linarith [h5]] at eq6
    nlinarith [sq_nonneg (x * y), sq_nonneg (a + b), sq_nonneg (a * x - b * y), sq_nonneg (a - b), sq_nonneg (x - y)]

  have eq4 : a * x^5 + b * y^5 = (x + y) * (a * x^4 + b * y^4) - x * y * (a * x^3 + b * y^3) := by 
    ring_nf

  rw [h4, h3, h5, h6] at eq4
  linarith [eq4]