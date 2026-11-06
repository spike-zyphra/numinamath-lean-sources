import Mathlib

theorem number_theory_279998 (n : ℕ) (h₀ : n > 0) (h₁ : n / 2 < 1000) (h₂ : n / 2 + 1000 = 746) :
    n / 2 = 1142 ∨ n / 2 = 944 := by 
  omega