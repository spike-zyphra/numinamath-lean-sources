import Mathlib

theorem number_theory_321252 (n : ℕ) (h₀ : n < 10000) (h₁ : n > 999)
    (h₂ : (n / 100) * (n % 100) + 10 * (n / 100) = n) (h₃ : n % 10 = 5) :
    n = 1995 := by
  interval_cases n <;> norm_num at h₂ h₃ ⊢ <;> omega