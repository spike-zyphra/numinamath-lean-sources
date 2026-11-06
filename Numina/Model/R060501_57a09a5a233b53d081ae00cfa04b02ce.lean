import Mathlib

theorem number_theory_175941 (n : ℕ) (h₀ : n > 0) (h₁ : (n - 1) - (n - 1 - 3 * (n - 1 - 3 * (n - 1))) = 10) :
    n = 45 := by
  omega