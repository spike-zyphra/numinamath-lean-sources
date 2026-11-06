import Mathlib

theorem algebra_204941 (a b c d : ℕ) (h₀ : a < b) (h₁ : c < d)
    (h₂ : a + b + c + d = 2017 - (a + b) - (c + d)) :
    a + b + c + d ≤ 806 := by
  omega