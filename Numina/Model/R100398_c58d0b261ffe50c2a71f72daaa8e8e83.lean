import Mathlib

theorem algebra_194131 (b : ℝ) (h₀ : b > 0) (h₁ : (3000 + b) / 15 = (3000 + b) / 20 + (3000 + b) / 24) :
    (3000 + b) / 20 = 100 := by
  have h2 : 3000 + b = 0 := by 
    linarith
  have h3 : b = -3000 := by
    linarith
  linarith