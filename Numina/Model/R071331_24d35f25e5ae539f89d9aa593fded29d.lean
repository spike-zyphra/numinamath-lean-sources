import Mathlib

theorem algebra_206966 (a b c d e : ℤ) (h₀ : a + b = -1) (h₁ : a + c = 4) (h₂ : a + d = 6)
    (h₃ : a + e = 9) (h₄ : b + c = 10) (h₅ : b + d = 11) (h₆ : b + e = 15) (h₇ : c + d = 16)
    (h₈ : c + e = 20) (h₉ : d + e = 22) :
    a * b * c * d * e = -4914 := by
  nlinarith [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉]