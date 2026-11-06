import Mathlib

theorem number_theory_268691 (n : ℕ) (h₀ : n % 3 = 1) (h₁ : (n - 1) % 4 = 1)
    (h₂ : (n - 2) % 5 = 1) :
    (n - 3) % 6 = 1 := by
  omega