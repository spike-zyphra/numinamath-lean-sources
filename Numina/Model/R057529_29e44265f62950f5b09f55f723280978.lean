import Mathlib

theorem number_theory_278359 (a b c : ℤ) (h₀ : a + b + c = 17 + 1967 + 1983) (h₁ : a - b - c = 17 + 1967 - 1983)
    (h₂ : b + a + c = 17 - 1967 + 1983) (h₃ : b - a - c = 17 - 1967 - 1983) :
    (a = 2 ∧ b = 2 ∧ c = 2) → False ∧ (a = 3 ∧ b = 3 ∧ c = 3) → True := by
  intro h1 h2
  exfalso
  linarith