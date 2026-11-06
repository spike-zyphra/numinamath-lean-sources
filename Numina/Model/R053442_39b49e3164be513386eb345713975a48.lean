import Mathlib

theorem algebra_272396 {n : ℕ} (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : (10 * (n % 10) + (n / 10)) - n = 54) :
    |(n % 10 : ℤ) - (n / 10 : ℤ)| = 6 := by
  have h3 : n = 10 * (n / 10) + (n % 10) := by
    omega
  rw [h3] at h₂
  have h4 : (n % 10 : ℤ) - (n / 10 : ℤ) = 6 := by
    omega
  rw [show (n % 10 : ℤ) - (n / 10 : ℤ) = 6 by linarith [h4]]
  norm_num