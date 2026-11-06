import Mathlib

theorem algebra_284703 (a b x y : ℝ)
    (h₁ : a * x + b * y = 3)
    (h₂ : a * x^2 + b * y^2 = 7)
    (h₃ : a * x^3 + b * y^3 = 16)
    (h₄ : a * x^4 + b * y^4 = 42) :
    a * x^5 + b * y^5 = 20 := by
  have eq1 : a * x^3 + b * y^3 = (x + y) * (a * x^2 + b * y^2) - x * y * (a * x + b * y) := by
    ring
  rw [h₁, h₂, h₃] at eq1
  -- Now we have the equation 16 = (x + y) * 7 - x * y * 3.
  have eq2 : a * x^4 + b * y^4 = (x + y) * (a * x^3 + b * y^3) - x * y * (a * x^2 + b * y^2) := by
    ring
  rw [h₂, h₃, h₄] at eq2
  -- Now we have the equation 42 = (x + y) * 16 - x * y * 7.
  have h5 : x + y = -14 := by
    nlinarith
  have h6 : x * y = -38 := by
    nlinarith
  have eq7 : a * x^5 + b * y^5 = (x + y) * (a * x^4 + b * y^4) - x * y * (a * x^3 + b * y^3) := by 
    ring
  rw [h₄, h₃] at eq7
  rw [show x + y = -14 by linarith [h5]] at eq7
  rw [show x * y = -38 by linarith [h6]] at eq7
  linarith