import Mathlib

theorem algebra_310783 (a b x y : ℝ)
    (h₁ : a * x + b * y = 3)
    (h₂ : a * x ^ 2 + b * y ^ 2 = 7)
    (h₃ : a * x ^ 3 + b * y ^ 3 = 16)
    (h₄ : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by
  have eq5 : a * x ^ 3 + b * y ^ 3 = (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) := by
    ring
  have eq6 : a * x ^ 4 + b * y ^ 4 = (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) := by
    ring
  have eq7 : a * x ^ 5 + b * y ^ 5 = (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
    ring
  rw [h₃, h₂, h₁] at eq5
  have eq8 : (x + y) * 7 - (x * y) * 3 = (16 : ℝ) := by linarith
  rw [h₄, h₃, h₂] at eq6
  have eq9 : (x + y) * 16 - (x * y) * 7 = (42 : ℝ) := by linarith
  have eq10 : x + y = -14 := by
    nlinarith
  have eq11 : x * y = -38 := by
    nlinarith
  rw [h₄, h₃, eq10, eq11] at eq7
  linarith