import Mathlib

theorem number_theory_14683 (n : ℕ) (h₀ : n < 500) (h₁ : n % 23 = 22) (h₂ : n % 21 = 14) :
  n = 413 := by 
  interval_cases n <;> omega