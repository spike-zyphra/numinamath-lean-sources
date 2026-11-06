import Mathlib

theorem algebra_172918 (a b c d : ℕ) (h₀ : a < b ∧ b < c ∧ c < d)
    (h₁ : a + b + c + d = 31) (h₂ : (a - 4) + (b - 4) + (c - 4) + (d - 4) = 16)
    (h₃ : (a - 7) + (b - 7) + (c - 7) + (d - 7) = 8) (h₄ : (a - 11) + (b - 11) +
    (c - 11) + (d - 11) = 1) :
    a = 3 ∧ b = 6 ∧ c = 10 ∧ d = 12 := by 
  omega