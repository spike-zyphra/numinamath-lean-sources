import Mathlib

theorem algebra_207009 (a b c d e : ℤ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : a ≠ d)
    (h₃ : a ≠ e) (h₄ : b ≠ c) (h₅ : b ≠ d) (h₆ : b ≠ e) (h₇ : c ≠ d) (h₈ : c ≠ e)
    (h₉ : d ≠ e) (h₁₀ : a + b = 5) (h₁₁ : a + c = 9) (h₁₂ : a + d = 10) (h₁₃ : a + e = 11)
    (h₁₄ : b + c = 12) (h₁₅ : b + d = 16) (h₁₆ : b + e = 16) (h₁₇ : c + d = 17)
    (h₁₈ : c + e = 21) (h₁₉ : d + e = 23) :
    a * b * c * d * e = 5292 := by 
  exfalso
  omega