import Mathlib

theorem number_theory_126 (n : ℕ) (h₀ : n ≥ 1000) (h₁ : n ≤ 9999) (h₂ : (n / 100) * (n % 100) * 2 = n) :
    n = 1352 := by
  interval_cases n <;> norm_num at *
  <;> omega