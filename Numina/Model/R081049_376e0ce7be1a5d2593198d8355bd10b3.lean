import Mathlib

theorem number_theory_148366 (n : ℕ) (h₀ : n > 99) (h₁ : n < 1000)
    (h₂ : (n / 100) % 10 + (n % 10) = 1) (h₃ : (n / 10) % 10 * (n / 100) % 10 = 4) :
    n = 140 := by
  interval_cases n <;> norm_num at h₀ h₁ h₂ h₃ <;> omega