import Mathlib

theorem inequalities_54122 (a b c d e : ℝ) (h₀ : a < b) (h₁ : b < c) (h₂ : c < d)
    (h₃ : d < e) (h₄ : a + b = 32) (h₅ : a + c = 36) (h₆ : b + c = 37)
    (h₇ : b + d = 48) (h₈ : c + d = 51) :
    e = 27.5 := by
  linarith