import Mathlib

theorem algebra_155185 (a b x y : ℝ) (h₁ : a * x + b * y = 3) (h₂ : a * x^2 + b * y^2 = 7)
    (h₃ : a * x^3 + b * y^3 = 16) (h₄ : a * x^4 + b * y^4 = 42) :
    a * x^5 + b * y^5 = 20 := by
  have eq1 : (x + y) * (a * x + b * y) = a * x^2 + b * y^2 + (a + b) * x * y := by
    ring
  rw [h₁, h₂] at eq1
  have eq2 : (x + y) * (a * x^2 + b * y^2) = a * x^3 + b * y^3 + (a * x + b * y) * x * y := by
    ring
  rw [h₂, h₃, h₁] at eq2
  have eq3 : (x + y) * (a * x^3 + b * y^3) = a * x^4 + b * y^4 + (a * x^2 + b * y^2) * x * y := by
    ring
  rw [h₃, h₄, h₂] at eq3
  nlinarith [sq_nonneg (x - y), sq_nonneg (a - b), sq_nonneg (x + y - (x + y)), sq_nonneg (x * y - (-38))]