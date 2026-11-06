import Mathlib

theorem number_theory_3398 (n : ℕ) (h₀ : 1000 ≤ n) (h₁ : n < 10000) (h₂ : 111 ∣ n)
    (h₃ : n / 111 = (Nat.digits 10 n).sum) :
    n = 2997 := by
  interval_cases n <;> norm_num at h₂ h₃ ⊢ <;> omega