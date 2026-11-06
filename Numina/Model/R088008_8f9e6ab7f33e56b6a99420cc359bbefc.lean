import Mathlib

theorem number_theory_808 (n : ℕ) (h₀ : n % 9 = 0) (h₁ : 10 ≤ n) (h₂ : n < 100)
    (h₃ : 7 ∣ n + 91) : n + 91 = 154 := by
  interval_cases n <;> omega