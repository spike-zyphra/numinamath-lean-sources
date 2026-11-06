import Mathlib

theorem number_theory_151359 :
    ¬∃ n : ℕ, (Nat.digits 10 (n ^ 58)).length = 64 := by 
  rintro ⟨n, hn⟩ 
  by_cases h3 : n > 0 
  · -- Assume n > 0. This implies n^58 > 0.
    have h4 : n ^ 58 > 0 := by 
      apply Nat.pow_pos
      linarith
    have h1 : n ^ 58 ≥ 10 ^ 63 := by
      by_contra h 
      push_neg at h 
      have h5 : (Nat.digits 10 (n ^ 58)).length < 64 := by 
        have h2 : n ^ 58 < 10 ^ 63 := by 
          omega 
        have h3 : (Nat.digits 10 (n ^ 58)).length = Nat.log 10 (n ^ 58) + 1 := by 
          rw [Nat.digits_len] 
          all_goals 
            have h4 : n ^ 58 > 0 := by
              apply Nat.pow_pos 
              linarith
            omega 
        rw [h3] 
        have h4 : Nat.log 10 (n ^ 58) < 63 := by 
          have h5 : n ^ 58 < 10 ^ 63 := by 
            omega 
          have h6 : Nat.log 10 (n ^ 58) < 63 := by 
            apply Nat.log_lt_of_lt_pow 
            all_goals 
              omega 
          linarith 
        omega
      omega
    have h2 : n ^ 58 < 10 ^ 64 := by
      by_contra h 
      push_neg at h 
      have h3 : (Nat.digits 10 (n ^ 58)).length > 64 := by 
        have h4 : n ^ 58 ≥ 10 ^ 64 := by 
          omega 
        have h5 : (Nat.digits 10 (n ^ 58)).length = Nat.log 10 (n ^ 58) + 1 := by 
          rw [Nat.digits_len] 
          all_goals
            have h4 : n ^ 58 > 0 := by 
              apply Nat.pow_pos 
              linarith
            omega 
        rw [h5] 
        have h6 : Nat.log 10 (n ^ 58) ≥ 64 := by 
          have h7 : n ^ 58 ≥ 10 ^ 64 := by 
            omega 
          have h8 : Nat.log 10 (n ^ 58) ≥ 64 := by 
            apply Nat.le_log_of_pow_le 
            all_goals 
              omega 
          omega 
        omega 
      omega
    have h3 : n ≤ 13 := by
      by_contra h
      push_neg at h 
      have h4 : n ≥ 14 := by linarith
      have h5 : n ^ 58 ≥ 14 ^ 58 := by 
        apply Nat.pow_le_pow_of_le_left 
        linarith 
      -- Now showing that 14^58 ≥ 10^64 to get a contradiction.
      have h6 : 14 ^ 58 ≥ 10 ^ 64 := by 
        norm_num
      have h7 : n ^ 58 ≥ 10 ^ 64 := by 
        linarith [h5, h6] 
      linarith
    interval_cases n <;> norm_num at h1 h2 hn <;> omega
  · -- Case n ≤ 0, which implies n = 0 
    have h4 : n = 0 := by 
      omega
    rw [h4] at hn 
    norm_num at hn