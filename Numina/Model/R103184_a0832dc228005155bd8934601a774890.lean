import Mathlib

theorem number_theory_271920 (a b c d e f : ℕ) (h₀ : a = b - 1) (h₁ : b = c - 1)
    (h₂ : c = d - 1) (h₃ : d = e - 1) (h₄ : e = f - 1) (h₅ : a + b + c + d + e + f = 108)
    (h₆ : d + e + f + a + b + c = 480) :
    f = 85 := by
  omega