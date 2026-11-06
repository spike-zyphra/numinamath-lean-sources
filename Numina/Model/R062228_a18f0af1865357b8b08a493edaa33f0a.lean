import Mathlib

theorem number_theory_235180 (n m : ℕ) (h₀ : n < 10) (h₁ : m < 10)
    (h₂ : 36 ∣ (1000 * n + 100 * m + 10 + 100 * n + 10 * m + 1)) :
    n = 9 ∧ m = 1 := by
  interval_cases n <;> interval_cases m <;> omega