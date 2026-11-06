import Mathlib

theorem algebra_239139 (a b c d : ℕ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : a = 84)
    (h₂ : b = 96)
    (h₃ : c = 65)
    (h₄ : d = 3 * (b + c)) :
    a + b + c + d = 728 := by 
  omega