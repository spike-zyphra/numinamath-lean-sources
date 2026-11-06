import Mathlib

theorem algebra_146004 (a b c d e f g : ℝ)
    (h₀ : c = a + b) (h₁ : d = b + c) (h₂ : e = c + d)
    (h₃ : f = d + e) (h₄ : e = 10) (h₅ : g = 0) :
    a + b + c + d + e + f = 40 := by 
  linarith [h₀, h₁, h₂, h₃, h₄]