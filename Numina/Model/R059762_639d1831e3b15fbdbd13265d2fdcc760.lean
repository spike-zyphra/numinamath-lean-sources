import Mathlib

theorem number_theory_94541 {k : ℕ} (h₀ : k > 0) (h₁ : (Nat.digits 10 n).length = 2)
    (h₂ : n = k * (Nat.digits 10 n).sum) :
    (10 * (Nat.digits 10 n).headI + (Nat.digits 10 n).tail.headI) =
    (Nat.digits 10 n).sum * (11 - k) := by 
  have h3 : n ≥ 10 := by
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h₁ <;> all_goals try { contradiction }
  
  have h4 : n < 100 := by
    by_contra h
    push_neg at h
    have h5 : (Nat.digits 10 n).length > 2 := by
      have h6 : n ≥ 100 := by linarith
      have h7 : (Nat.digits 10 n).length ≥ 3 := by
        have : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by
          rw [Nat.digits_len]
          all_goals linarith
        rw [this]
        have h9 : Nat.log 10 n ≥ 2 := by
          have : 10 ^ 2 ≤ n := by linarith
          have h9 : Nat.log 10 n ≥ 2 := by
            apply Nat.le_log_of_pow_le (by linarith) this
          linarith
        linarith
      linarith
    omega

  interval_cases n <;> norm_num at h₁ h₂ ⊢ <;> omega