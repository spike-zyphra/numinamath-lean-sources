import Mathlib

theorem number_theory_279596 (a b c d e : ℤ) (h₀ : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e)
    (h₁ : b ≠ c ∧ b ≠ d ∧ b ≠ e) (h₂ : c ≠ d ∧ c ≠ e) (h₃ : d ≠ e)
    (h₄ : a + b + c = 7) (h₅ : a + b + d = 11) (h₆ : a + b + e = 13)
    (h₇ : a + c + d = 14) (h₈ : a + c + e = 19) (h₉ : a + d + e = 21)
    (h₁₀ : b + c + d = 22) (h₁₁ : b + c + e = 25) (h₁₂ : b + d + e = 26)
    (h₁₃ : c + d + e = 28) :
    a + b + c + d + e = 31 := by
  linarith