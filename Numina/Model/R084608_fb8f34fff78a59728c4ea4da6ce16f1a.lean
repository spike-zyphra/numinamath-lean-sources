import Mathlib

theorem number_theory_104246 (a b c d : ℕ) (h₀ : a + b + c + d > 70)
    (h₁ : a + b = 7) (h₂ : a + c = 9) (h₃ : a + d = 10) (h₄ : b + c = 12)
    (h₅ : b + d = 15) (h₆ : c + d = 16) (h₇ : a + b + c + d = 19) (h₈ : a + b + c + d = 21) :
    max (max a b) (max c d) = 33 := by 
  omega