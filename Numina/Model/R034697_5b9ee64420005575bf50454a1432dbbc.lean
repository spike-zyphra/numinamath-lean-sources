import Mathlib

theorem algebra_96353 {b c : ℝ} (h : ∀ x, (x + 2) * (x + b) = x ^ 2 + c * x + 6) : c = 5 := by
  have eq1 := h 0
  have eq2 : 2 * b = 6 := by
    linarith
  
  have h1 : b = 3 := by 
    linarith
  
  have eq3 := h 1
  rw [h1] at eq3
  linarith