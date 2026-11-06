import Mathlib

theorem algebra_232432 {n : ℕ} (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : (10 * n + 100) / (n + 1) = 37 * (n + 1)) :
    n = 27 := by
  interval_cases n <;> norm_num at h₂ <;> omega