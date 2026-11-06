import Mathlib

theorem algebra_8742 {a b x y : ℝ} (h1 : a * x + b * y = 1) (h2 : a * x^2 + b * y^2 = 2)
    (h3 : a * x^3 + b * y^3 = 7) (h4 : a * x^4 + b * y^4 = 18) :
    a * x^5 + b * y^5 = 163 / 3 := by

  have eq1 : a * x^3 + b * y^3 = (a * x^2 + b * y^2) * (x + y) - (x * y) * (a * x + b * y) := by
    ring

  rw [h2, h1] at eq1
  rw [h3] at eq1

  have eq2 : a * x^4 + b * y^4 = (a * x^3 + b * y^3) * (x + y) - (x * y) * (a * x^2 + b * y^2) := by
    ring

  rw [h3, h2] at eq2
  rw [h4] at eq2

  have h5 : x + y = 4 / 3 := by
    nlinarith [eq1, eq2]

  have h6 : x * y = -13 / 3 := by
    nlinarith [eq1, eq2, h5]

  have eq3 : a * x^5 + b * y^5 = (a * x^4 + b * y^4) * (x + y) - (x * y) * (a * x^3 + b * y^3) := by
    ring

  rw [h4, h5, h6, h3] at eq3

  linarith