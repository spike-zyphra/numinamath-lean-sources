import Mathlib

theorem algebra_13218 (a b c d : ℕ)
    (h₀ : a + b + c + d = 78)
    (h₁ : b = 2 * a)
    (h₂ : c = 3 * b)
    (h₃ : d = 5 * c) :
    a = 2 := by 
  omega