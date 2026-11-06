import Mathlib

theorem number_theory_256240 (n : ℕ) (h₀ : n < 120) (h₁ : 10 * 6 < n) (h₂ : 10 * 7 < n)
    (h₃ : n % 6 = 0) (h₄ : n % 7 = 0) : n = 84 := by
  interval_cases n <;> omega