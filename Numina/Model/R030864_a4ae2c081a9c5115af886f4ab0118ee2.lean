import Mathlib

theorem number_theory_16417 :
    IsLeast {n | n ≥ 1000 ∧ ∃ k, k^2 = n ∧ ∃ m, m^3 = n} 4096 := by
  constructor
  · -- Show that 4096 is in the set
    constructor
    · norm_num 
    · use 64
      constructor
      · norm_num
      · use 16
        all_goals norm_num
  · -- Show that no number less than 4096 is in the set.
    intro n hn
    rcases hn with ⟨hn1, k, hk, m, hm⟩
    by_contra h
    push_neg at h
    have h1 : k^2 = n := by linarith [hk]
    have h2 : m^3 = n := by linarith [hm]
    have h3 : k < 64 := by nlinarith [h1, h]
    have h4 : m < 16 := by
      have hm1 : m^3 = n := h2
      have hm2 : m^3 < (4096 : ℕ) := by linarith [hm1, h]
      by_contra h5
      push_neg at h5
      have h6 : m ≥ 16 := by omega
      have h7 : m^3 ≥ 4096 := by
        have : m ≥ 16 := h6
        have h11 : m^3 ≥ 16^3 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals omega
        have h8 : (16 : ℕ) ^3 = 4096 := by norm_num
        nlinarith [h11, h8]
      omega
    have h5 : m ≥ 10 := by
      by_contra h6
      push_neg at h6
      have h7 : m < 10 := by omega
      have h8 : m^3 < 1000 := by
        have h11 : m < 10 := h7
        have h22 : m^3 < (10 : ℕ) ^3 := by
          apply Nat.pow_lt_pow_left
          all_goals 
            omega
        have h33 : (10 : ℕ) ^3 = 1000 := by norm_num
        linarith [h22, h33]
      have h9 : n < 1000 := by linarith [h8, h2]
      omega
    interval_cases m <;> try { 
      norm_num [pow_succ, pow_zero] at hm h2 ⊢
      all_goals
      try { 
        have : k ≤ 63 := by nlinarith
        interval_cases k <;> omega 
      }
      <;> try { 
        exfalso 
        <;> omega 
      }
    }