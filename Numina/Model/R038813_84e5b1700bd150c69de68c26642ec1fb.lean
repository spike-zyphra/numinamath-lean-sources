import Mathlib

theorem number_theory_298811 (a b : ℕ) (ha : a > 0) (hb : b > 0)
    (h1 : (Nat.digits 10 (a ^ 100)).length = 120) (h2 : (Nat.digits 10 (a ^ b)).length = 10) :
    b = 8 := by
  have h1' : a ^ 100 ≥ 10 ^ 119 := by
    by_contra h
    push_neg at h
    have h_pos : a ^ 100 > 0 := by positivity
    have : (Nat.digits 10 (a ^ 100)).length < 120 := by
      have h3 : a ^ 100 < 10 ^ 119 := by linarith
      have : a ^ 100 < 10 ^ 119 := h3
      have h4 : Nat.log 10 (a ^ 100) < 119 := by
        have h5 : a ^ 100 < 10 ^ 119 := h3
        have h6 : Nat.log 10 (a ^ 100) < 119 := by
          apply Nat.log_lt_of_lt_pow
          all_goals
            -- Note: we can't use nlinarith here, which might need linarith.
            have h12 : a ^ 100 < 10 ^ 119 := h3
            norm_num at h12 ⊢
            all_goals
              omega
        omega
      have h7 : (Nat.digits 10 (a ^ 100)).length = Nat.log 10 (a ^ 100) + 1 := by
        rw [Nat.digits_len]
        all_goals
          try { omega }
          try { positivity }
          all_goals tauto
      rw [h7]
      omega
    linarith
  -- h1''

  have h1'' : a ^ 100 < 10 ^ 120 := by
    by_contra h
    push_neg at h
    have h_pos : a ^ 100 > 0 := by positivity
    have : (Nat.digits 10 (a ^ 100)).length > 120 := by
      have h3 : a ^ 100 ≥ 10 ^ 120 := by linarith
      have h3 : a ^ 100 ≥ 10 ^ 120 := h3
      have h4 : Nat.log 10 (a ^ 100) ≥ 120 := by
        have h5 : a ^ 100 ≥ 10 ^ 120 := h3
        have h6 : Nat.log 10 (a ^ 100) ≥ 120 := by
          apply Nat.le_log_of_pow_le
          all_goals
            norm_num at h5 ⊢
            try { omega }
            all_goals try { 
              omega
            }
        omega
      have h7 : (Nat.digits 10 (a ^ 100)).length = Nat.log 10 (a ^ 100) + 1 := by
        rw [Nat.digits_len]
        all_goals
          try { omega }
          try { positivity }
          all_goals tauto
      rw [h7]
      omega
    linarith
  -- h1''

  have h2' : a ^ b ≥ 10 ^ 9 := by
    by_contra h
    push_neg at h
    have h_pos : a ^ b > 0 := by positivity
    have : (Nat.digits 10 (a ^ b)).length < 10 := by
      have h3 : a ^ b < 10 ^ 9 := by linarith
      have h3 : a ^ b < 10 ^ 9 := h3
      have h4 : Nat.log 10 (a ^ b) < 9 := by
        have h5 : a ^ b < 10 ^ 9 := h3
        have h6 : Nat.log 10 (a ^ b) < 9 := by
          apply Nat.log_lt_of_lt_pow
          all_goals
            norm_num at h5 ⊢
            try { omega }
        omega
      have h7 : (Nat.digits 10 (a ^ b)).length = Nat.log 10 (a ^ b) + 1 := by
        rw [Nat.digits_len]
        all_goals
          try { omega }
          try { positivity }
          all_goals tauto
      rw [h7]
      omega
    linarith
  -- h2''

  have h2'' : a ^ b < 10 ^ 10 := by
    by_contra h
    push_neg at h
    have h_pos : a ^ b > 0 := by positivity
    have : (Nat.digits 10 (a ^ b)).length > 10 := by
      have h3 : a ^ b ≥ 10 ^ 10 := by linarith
      have h3 : a ^ b ≥ 10 ^ 10 := h3
      have h4 : Nat.log 10 (a ^ b) ≥ 10 := by
        have h5 : a ^ b ≥ 10 ^ 10 := h3
        have h6 : Nat.log 10 (a ^ b) ≥ 10 := by
          apply Nat.le_log_of_pow_le
          all_goals
            norm_num at h5 ⊢
            try { omega }
            try { 
              omega
            }
        omega
      have h7 : (Nat.digits 10 (a ^ b)).length = Nat.log 10 (a ^ b) + 1 := by
        rw [Nat.digits_len]
        all_goals
          try { omega }
          try { positivity }
          all_goals tauto
      rw [h7]
      omega
    linarith
  -- Final

  have h3 : b = 8 := by
    have h100 : a ^ 100 ≥ 10 ^ 119 := h1'
    have h100' : a ^ 100 < 10 ^ 120 := h1''
    have h2b : a ^ b ≥ 10 ^ 9 := h2'
    have h2b' : a ^ b < 10 ^ 10 := h2''
    
    have h4 : a ≤ 19 := by
      by_contra h
      push_neg at h
      have h3 : a ≥ 20 := by nlinarith
      have h4 : a ^ 100 ≥ 20 ^ 100 := by
        apply Nat.pow_le_pow_of_le_left
        all_goals nlinarith
      norm_num at h4
      all_goals linarith
    interval_cases a <;> try { 
      have h100 : a ^ 100 ≥ 10 ^ 119 := h1'
      norm_num at h100
      all_goals try { 
        have h100' : a ^ 100 < 10 ^ 120 := h1''
        norm_num at h100'
        all_goals try { 
          have h2b : a ^ b ≥ 10 ^ 9 := h2'
          norm_num at h2b
          have h2b' : a ^ b < 10 ^ 10 := h2''
          norm_num at h2b'
          all_goals try { 
            have : b = 8 := by
              have h1 : b ≤ 20 := by
                have : a ^ b < 10 ^ 10 := h2''
                have h1 : b ≤ 20 := by
                  by_contra h
                  push_neg at h
                  have : a ^ b ≥ 2 ^ 21 := by
                    have : a ≥ 2 := by nlinarith
                    have : a ^ b ≥ 2 ^ 21 := by
                      have h5 : b ≥ 21 := by omega
                      have h6 : a ^ b ≥ 2 ^ 21 := by
                        apply Nat.pow_le_pow_of_le_left
                        all_goals nlinarith
                      linarith
                    linarith
                  norm_num at this
                  all_goals linarith
                omega
              interval_cases b <;> try { 
                omega
              }
              <;> norm_num
              <;> try { 
                omega
              }
            linarith
          }
          all_goals try { 
            omega
          }
        }
        all_goals try { 
          omega
        }
      }
      all_goals try { 
        omega
      }
    }
    all_goals try { 
      omega
    }
  exact h3