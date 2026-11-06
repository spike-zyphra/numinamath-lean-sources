import Mathlib

theorem algebra_121285 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : 402 * n % 100 = 0) : 10 * (402 * n / 100) = 2010 := by
  have h3 : n = 50 := by 
    interval_cases n <;> norm_num at h₂ <;> omega
  subst h3
  norm_num