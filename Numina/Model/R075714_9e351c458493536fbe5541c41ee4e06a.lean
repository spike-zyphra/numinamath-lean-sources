import Mathlib

theorem algebra_97615 (a b c d : ℕ) (h₀ : a ≤ 100) (h₁ : b ≤ 100)
    (h₂ : c ≤ 100) (h₃ : d ≤ 100) (h₄ : (a + b + c + d) / 4 = 95)
    (h₅ : a = 97) (h₆ : b = 91) :
    c ≥ 92 := by
  subst h₅
  subst h₆
  omega