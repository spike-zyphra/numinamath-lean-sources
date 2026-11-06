import Mathlib

theorem algebra_320508 {a b x y : ℝ} (h₁ : a * x + b * y = 3) (h₂ : a * x ^ 2 + b * y ^ 2 = 7)
    (h₃ : a * x ^ 3 + b * y ^ 3 = 16) (h₄ : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by

  have eq1 : a * x ^ 3 + b * y ^ 3 = (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) := by 
    ring
  rw [h₁, h₂, h₃] at eq1

  have eq2 : a * x ^ 4 + b * y ^ 4 = (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) := by
    ring
  rw [h₂, h₃, h₄] at eq2
  
  have h5 : (x + y) = -14 := by
    nlinarith
  
  have h6 : x * y = -38 := by
    nlinarith
  
  have eq3 : a * x ^ 5 + b * y ^ 5 = (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
    ring
  
  rw [h₄, h₃, h5, h6] at eq3
  linarith