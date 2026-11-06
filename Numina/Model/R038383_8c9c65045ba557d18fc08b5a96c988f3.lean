import Mathlib

theorem number_theory_161208 (n : ℕ) (h₀ : n < 10000) (h₁ : n > 999)
    (h₂ : 2 * n = 9 * (1000 * (n % 10) + 100 * ((n / 10) % 10) +
      10 * ((n / 100) % 10) + (n / 1000))) :
    n = 8991 ∨ n = 8181 := by
  interval_cases n <;> norm_num at h₂ <;> omega