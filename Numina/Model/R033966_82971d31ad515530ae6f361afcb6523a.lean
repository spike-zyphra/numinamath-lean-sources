import Mathlib

theorem algebra_327558 {a b x y : ℝ}
    (h1 : a * x + b * y = 3)
    (h2 : a * x ^ 2 + b * y ^ 2 = 7)
    (h3 : a * x ^ 3 + b * y ^ 3 = 16)
    (h4 : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by

  have eq1 : a * x ^ 3 + b * y ^ 3 = (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) := by
    ring

  rw [h3, h2, h1] at eq1

  have eq2 : a * x ^ 4 + b * y ^ 4 = (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) := by
    ring

  rw [h4, h3, h2] at eq2

  have h5 : x + y = -14 := by
    nlinarith

  have h6 : x * y = -38 := by
    nlinarith

  have eq3 : a * x ^ 5 + b * y ^ 5 = (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
    ring

  rw [eq3]
  rw [h5, h4, h6, h3]
  norm_num