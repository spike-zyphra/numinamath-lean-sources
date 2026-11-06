import Mathlib

theorem number_theory_252266 (N : ℕ) (h₀ : N % 2 = 0) (h₁ : N % 4 = 0) (h₂ : N % 12 = 0)
    (h₃ : ¬N % 24 = 0) :
    ¬(N % 24 = 0) := by 
  exact h₃