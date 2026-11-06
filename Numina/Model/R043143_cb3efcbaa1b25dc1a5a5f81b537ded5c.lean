import Mathlib


theorem number_theory_14370 : IsLeast {k : ℕ | ∃ n : ℕ, (Nat.digits 10 n).length = 4 ∧ 2 ∣ n ∧
    323 ∣ n ∧ k ∣ n ∧ 323 < k} 340 := by
  constructor 
  · -- Show 340 is in the set
    use 6460 
    native_decide 
  · -- Show 340 is the minimal 
    intro k hk
    rcases hk with ⟨n, hn1, hn2, hn3, hk1, hk2⟩
    by_contra h
    push_neg at h
    have h1 : k ≤ 339 := by 
      omega 
    have h2 : n ≥ 1000 := by 
      by_contra h
      push_neg at h
      interval_cases n <;> norm_num at hn1 
      all_goals 
        try { contradiction }
    have h3 : n ≤ 9999 := by 
      by_contra h
      push_neg at h
      have h4 : (Nat.digits 10 n).length > 4 := by
        have h5 : n > 9999 := by linarith
        have h6 : (Nat.digits 10 n).length > 4 := by
          have h7 : Nat.log 10 n ≥ 4 := by 
            apply Nat.le_log_of_pow_le (by omega) h5 
          have h8 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by 
            rw [Nat.digits_len] 
            all_goals 
              omega 
          omega 
        omega 
      omega 
    have h4 : 323 ∣ n := hn3
    obtain ⟨t, ht⟩ := h4
    rw [show n = 323 * t by linarith [ht]] at hk1 hn2 h2 h3
    have ht8 : t ≥ 4 := by
      nlinarith 
    have ht9 : t ≤ 30 := by
      nlinarith 
    interval_cases t <;> try { 
      omega 
    } <;> try { 
      interval_cases k <;> omega 
    }