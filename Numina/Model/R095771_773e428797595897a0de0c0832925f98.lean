import Mathlib

theorem number_theory_188038 (n : ℕ) (h₀ : n > 200) (h₁ : n < 300)
    (h₂ : n % 25 = 10) (h₃ : n % 30 = 15) :
    n = 285 := by
  interval_cases n <;> omega