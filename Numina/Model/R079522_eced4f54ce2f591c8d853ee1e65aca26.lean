import Mathlib

theorem number_theory_98094 {n : ℕ} (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : (Nat.digits 10 n).prod + (Nat.digits 10 n).sum = n) :
    n % 10 = 9 := by
  interval_cases n <;> norm_num at h₂ ⊢ <;> all_goals omega