import Mathlib

theorem number_theory_107762 (n : ℕ) (h₀ : n < 1000000) (h₁ : (2 * 100000 + n) / 10 = 3 * n) :
    n = 285714 := by
  omega