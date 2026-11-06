import Mathlib

theorem algebra_145563 (a b x y : ℝ)
    (h₁ : a * x + b * y = 3)
    (h₂ : a * x^2 + b * y^2 = 7)
    (h₃ : a * x^3 + b * y^3 = 16)
    (h₄ : a * x^4 + b * y^4 = 42) :
    a * x^5 + b * y^5 = 20 := by
  have eq1 : a * x^2 + b * y^2 = (x + y) * (a * x + b * y) - (x * y) * (a + b) := by
    ring_nf
  rw [h₁] at eq1
  have eq2 : 7 = (x + y) * 3 - (x * y) * (a + b) := by 
    linarith [h₂, eq1]
  have eq3 : a * x^3 + b * y^3 = (x + y) * (a * x^2 + b * y^2) - (x * y) * (a * x + b * y) := by
    ring_nf
  rw [h₂, h₁] at eq3
  have eq4 : 16 = (x + y) * 7 - (x * y) * 3 := by 
    linarith [h₃, eq3]
  have eq5 : a * x^4 + b * y^4 = (x + y) * (a * x^3 + b * y^3) - (x * y) * (a * x^2 + b * y^2) := by 
    ring_nf
  rw [h₃, h₂] at eq5
  have eq6 : 42 = (x + y) * 16 - (x * y) * 7 := by 
    linarith [h₄, eq5]
  have h5 : x + y = -14 := by
    nlinarith [sq_nonneg (x + y + 14), sq_nonneg (x * y + 38)]
  have h6 : x * y = -38 := by
    rw [h5] at eq4
    linarith
  have eq7 : a * x^5 + b * y^5 = (x + y) * (a * x^4 + b * y^4) - (x * y) * (a * x^3 + b * y^3) := by
    ring_nf
  rw [h₄, h₃, h5, h6] at eq7
  linarith [eq7]