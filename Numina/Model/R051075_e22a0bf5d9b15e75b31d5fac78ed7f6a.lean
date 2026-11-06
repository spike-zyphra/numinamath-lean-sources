import Mathlib

theorem algebra_243862 (a b c d : ℤ) (h₀ : a < b) (h₁ : a < c) (h₂ : a < d)
    (h₃ : b < c) (h₄ : b < d) (h₅ : c < d) (h₆ : (a + b + c) / 3 + d = 17)
    (h₇ : (a + b + d) / 3 + c = 21) (h₈ : (a + c + d) / 3 + b = 23) (h₉ : (b + c + d) / 3 + a = 29) :
    d = 21 := by 
  omega