import Mathlib

theorem algebra_116838 (a b c d e : ℕ) (h₀ : a = 2 * b) (h₁ : b = 11) (h₂ : c = d / 2)
    (h₃ : d = e / 2) (h₄ : (a + b + c + d + e) / 5 = 24) :
    (a + b + c + d + e) / 5 = 24 := by
  exact h₄