import Mathlib

theorem number_theory_258544 (n : ℕ) (h₀ : n < 10000) (h₁ : 99 ∣ n) :
    18 ∣ (Nat.digits 10 n).sum := by
  interval_cases n <;> norm_num at h₁ ⊢ <;> omega