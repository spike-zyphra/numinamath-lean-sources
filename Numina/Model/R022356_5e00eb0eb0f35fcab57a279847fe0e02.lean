import Mathlib

theorem number_theory_253569 (n : ℕ) (h₀ : n < 10000) (h₁ : 99 ∣ n) :
    18 ∣ (Nat.digits 10 n).sum := by 
  have h2: (Nat.digits 10 n).sum % 2 = 0 := by
    interval_cases n <;> norm_num at h₁ ⊢ 
  -- Use divisibility by 9
  have h3: (Nat.digits 10 n).sum % 9 = 0 := by
    have h9 : n % 9 = 0 := by 
      omega
    have h8 : (Nat.digits 10 n).sum % 9 = n % 9 := by
      rw [Nat.modEq_nine_digits_sum (n)]
    rw [h9] at h8
    omega
  omega