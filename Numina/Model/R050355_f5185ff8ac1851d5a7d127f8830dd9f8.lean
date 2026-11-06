import Mathlib

theorem number_theory_118425 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : n % 13 = (n / 11)) (h₃ : n % 11 = (n / 13)) :
    n = 71 := by
  interval_cases n <;> omega