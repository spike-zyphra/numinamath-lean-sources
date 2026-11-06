import Mathlib

theorem algebra_96805 
  (a b c d e : ℕ) 
  (h₀ : 2 * a = b) 
  (h₁ : 2 * b = c) 
  (h₂ : 2 * c = d) 
  (h₃ : 2 * d = e) 
  (h₄ : e = 48) : 
  a = 3 := 
by
  have h₅ : d = 24 := by 
    linarith [h₃, h₄]
  have h₆ : c = 12 := by 
    linarith [h₂, h₅]
  have h₇ : b = 6 := by 
    linarith [h₁, h₆]
  have h₈ : a = 3 := by 
    linarith [h₀, h₇]
  exact h₈