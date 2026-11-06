import Mathlib

theorem algebra_306425 (a b c d e f g h : ℝ)
    (h₀ : a = (b + c + d) / 3) (h₁ : b = (a + e + f) / 3)
    (h₂ : c = (a + g + h) / 3) (h₃ : d = (a + h + g) / 3)
    (h₄ : e = (b + f + g) / 3) (h₅ : f = (b + e + h) / 3)
    (h₆ : g = (c + e + h) / 3) (h₇ : h = (d + f + g) / 3) :
    a + b + c + d - (e + f + g + h) = 0 := by
  linarith