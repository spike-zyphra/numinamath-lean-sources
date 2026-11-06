import Mathlib

theorem number_theory_16028 (k : ℕ) (h₀ : 0 < k) (h₁ : 60 % (k ^ 2) = 6) :
    100 % k = 1 := by
  have h2 : k ≤ 7 := by
    by_contra h
    push_neg at h
    have h3 : k ^ 2 ≥ 64 := by
      have h4 : k ≥ 8 := by omega
      have h5 : k ^ 2 ≥ 8 ^ 2 := by
        apply Nat.pow_le_pow_of_le_left h4 2
      norm_num at h5 ⊢
      linarith
    have h4 : 60 % (k ^ 2) = 60 := by
      rw [Nat.mod_eq_of_lt]
      all_goals 
        omega
    omega
  interval_cases k <;> norm_num at h₁ ⊢ <;> omega