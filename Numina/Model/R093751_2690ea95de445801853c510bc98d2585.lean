import Mathlib

theorem algebra_14471 (a b c d e : ℕ)
    (h₀ : a + b + c + d + e = 100)
    (h₁ : b = a + 6)
    (h₂ : c = b + 6)
    (h₃ : d = c + 6)
    (h₄ : e = d + 6) :
    c = 20 := by 
  omega