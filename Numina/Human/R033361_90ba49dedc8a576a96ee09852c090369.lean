import Mathlib

theorem algebra_239091 (a b c d : ℕ) (h₀ : a * c + a * d + b * c + d * b = 68) (h₁ : c + d = 4) :
    a + b + c + d = 21 := by 
  have h2 : (a + b) * (c + d) = 68 := by 
    linarith [h₀]
  rw [h₁] at h2
  have h3 : (a + b) * 4 = 68 := h2
  have h4 : a + b = 17 := by 
    omega
  omega