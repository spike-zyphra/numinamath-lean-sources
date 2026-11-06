import Mathlib

theorem number_theory_275604 (n m : ℕ) (h₀ : n + m + (10 - n - m) = 10) :
    3 * n - 0 * m + 1 * (10 - n - m) ≠ 29 := by
  omega