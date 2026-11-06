import Mathlib

theorem number_theory_233035 (n : ℕ) (h₀ : n % 10 = 2) (h₁ : (n / 100) + (n % 100) * 100 = n + 180) :
    n = 2022 := by
  omega