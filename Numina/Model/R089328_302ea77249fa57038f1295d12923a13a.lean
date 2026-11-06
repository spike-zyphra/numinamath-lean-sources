import Mathlib

theorem algebra_127149 (a b c d : ℤ) :
    (a * 19^3 + b * 19^2 + c * 19 + d ≠ 1) ∨ (a * 62^3 + b * 62^2 + c * 62 + d ≠ 2) := by 
  by_contra h
  push_neg at h
  
  have h1 : a * 19^3 + b * 19^2 + c * 19 + d = 1 := h.1
  have h2 : a * 62^3 + b * 62^2 + c * 62 + d = 2 := h.2
  
  have eq1 : a * 62^3 + b * 62^2 + c * 62 + d - (a * 19^3 + b * 19^2 + c * 19 + d) = 1 := by 
    linarith
  
  have eq2 : a * 62^3 + b * 62^2 + c * 62 + d - (a * 19^3 + b * 19^2 + c * 19 + d) =
      a * (62^3 - 19^3) + b * (62^2 - 19^2) + c * (62 - 19) := by 
      ring
  
  rw [eq2] at eq1
  
  have eq3 : a * (62^3 - 19^3) + b * (62^2 - 19^2) + c * (62 - 19) = 43 * (a * (62^2 + 62*19 + 19^2) + b * 81 + c) := by 
    ring
  
  rw [eq3] at eq1
  
  have h3 : 43 ∣ 1 := by 
    omega
  
  all_goals omega