import Mathlib

theorem algebra_183170 (a b x y : ℝ)
    (h₀ : a * x + b * y = 3)
    (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
    (h₂ : a * x ^ 3 + b * y ^ 3 = 16)
    (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by

  have eq1 : a * x ^ 3 + b * y ^ 3 = (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) := by 
    ring
  rw [h₁, h₂, h₀] at eq1

  have eq2 : a * x ^ 4 + b * y ^ 4 = (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) := by 
    ring
  rw [h₂, h₃, h₁] at eq2

  have eq3 : x + y = -14 := by 
    nlinarith

  have eq4 : x * y = -38 := by
    nlinarith [eq1, eq2, eq3]

  have eq5 : a * x ^ 5 + b * y ^ 5 = (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by 
    ring

  rw [eq5, h₃, h₂, eq3, eq4]
  norm_num