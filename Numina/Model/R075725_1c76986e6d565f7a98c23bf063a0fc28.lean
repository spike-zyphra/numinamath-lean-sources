import Mathlib

theorem number_theory_232370 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : (n / 10) % 10 = n - (10 * (n % 10) + (n / 10))) :
    n = 98 := by
  interval_cases n <;> omega