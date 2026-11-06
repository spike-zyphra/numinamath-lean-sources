import Mathlib

theorem algebra_294079 {a b : ℝ} (h : ∀ x : ℝ, a * (a - x) - b * (b - x) = 0) : a - b = 0 := by

  have eq1 := h 0
  have eq2 : a^2 - b^2 = 0 := by 
    linarith
  
  have eq3 := h 1
  have eq4 : a^2 - a - b^2 + b = 0 := by
    linarith
  
  have eq5 : (a^2 - b^2) - (a - b) = 0 := by 
    linarith
  
  have h3 : - (a - b) = 0 := by 
    linarith [eq2, eq4]
  
  linarith