import Mathlib

theorem algebra_285007 (a b c d e : ℝ)
    (h₀ : (a + b + c + d + e) / 5 = 90)
    (h₁ : (a + b + c) / 3 = 86)
    (h₂ : (b + d + e) / 3 = 95) :
    b = 93 := by
  linarith