import Mathlib

theorem number_theory_279371 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : n / (n % 10) = 9) (h₃ : n % (n % 10) = 6) :
    n = 78 := by
  interval_cases n <;> norm_num at *
  <;> omega