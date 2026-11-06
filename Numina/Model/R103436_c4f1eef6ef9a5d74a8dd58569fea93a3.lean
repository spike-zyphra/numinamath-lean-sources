import Mathlib

theorem algebra_4111 {n : ℕ} (h₀ : n < 100) (h₁ : n > 9) (h₂ : (Nat.digits 10 n).sum = 11)
    (h₃ : 10 * (n % 10) + (n / 10) = n - 27) : n = 74 := by 
  interval_cases n <;> norm_num at h₂ h₃ ⊢ <;> omega