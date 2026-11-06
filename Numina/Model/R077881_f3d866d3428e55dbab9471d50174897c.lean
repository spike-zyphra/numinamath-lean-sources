import Mathlib

theorem algebra_11429
(a b c : ℝ)
(h₀ : 0 < a)
(h₁ : 0 < b)
(h₂ : 0 < c)
(h₃ : a * (b + c) = 152)
(h₄ : b * (c + a) = 162)
(h₅ : c * (a + b) = 170) :
a * b * c = 720 := by
  have eq1 : a * b + a * c = 152 := by
    nlinarith
  have eq2 : a * b + b * c = 162 := by
    nlinarith
  have eq3 : a * c + b * c = 170 := by
    nlinarith
  have eq4 : a * b = 72 := by
    nlinarith [eq1, eq2, eq3]
  have eq5 : b * c = 90 := by
    nlinarith [eq1, eq2, eq3]
  have eq6 : a * c = 80 := by
    nlinarith [eq1, eq2, eq3]
  nlinarith [eq4, eq5, eq6, mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂]