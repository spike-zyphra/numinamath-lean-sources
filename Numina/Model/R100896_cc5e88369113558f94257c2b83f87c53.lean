import Mathlib

theorem algebra_209109 (d p c : ℝ) (h₀ : d > 0) (h₁ : p > 0) (h₂ : c > 0)
    (h₃ : (2 / 5) * d = p * (1 - (2 / 5)) + c * (2 / 5)) (h₄ : (3 / 5) * d = p * (1 - (3 / 5)) + c * (3 / 5)) :
    c / p = 5 := by
  have eq1 : 2 * d = 3 * p + 2 * c := by 
    linarith 

  have eq2 : 3 * d = 2 * p + 3 * c := by
    linarith

  have h7 : p = 0 := by 
    linarith [eq1, eq2]

  linarith