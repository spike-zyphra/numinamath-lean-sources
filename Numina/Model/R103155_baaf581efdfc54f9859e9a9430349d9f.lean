import Mathlib

theorem algebra_173131 (a b c d : ℕ) (h₀ : a < b ∧ b < c ∧ c < d)
    (h₁ : a + b + c + d = 33) (h₂ : (a - 3) + (b - 3) + (c - 3) + (d - 3) = 22)
    (h₃ : (a - 7) + (b - 7) + (c - 7) + (d - 7) = 11) (h₄ : (a - 13) + (b - 13) +
    (c - 13) + (d - 13) = 1) :
    a = 2 ∧ b = 6 ∧ c = 11 ∧ d = 14 := by
  omega