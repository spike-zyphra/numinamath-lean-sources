import Mathlib

theorem algebra_183460 {n : ℕ} (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : n = (n / 10) + (n % 10)^2) :
    n = 89 := by
  interval_cases n <;> norm_num at h₂ <;> omega