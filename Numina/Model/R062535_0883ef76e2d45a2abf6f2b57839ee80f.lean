import Mathlib

theorem algebra_3191 (a b c d e : ℤ) (h₀ : a ≤ b) (h₁ : b ≤ c) (h₂ : c ≤ d) (h₃ : d ≤ e)
    (h₄ : (a + b + c + d)/4 = 3075/100) (h₅ : (a + b + c + e)/4 = 2950/100)
    (h₆ : (a + b + d + e)/4 = 3025/100) (h₇ : (a + c + d + e)/4 = 3100/100) :
    c = 28 := by 
  omega