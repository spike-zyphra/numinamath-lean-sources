import Mathlib

theorem number_theory_109846 (n : ℕ) (h₀ : n > 0) (h₁ : (10 * n + 1) % 1000000 = 3 * n) :
    n = 142857 := by
  omega