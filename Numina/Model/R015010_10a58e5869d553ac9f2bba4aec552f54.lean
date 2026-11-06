import Mathlib

theorem number_theory_5516 {n : ℕ} (hn : n ^ n = 302875106592253) : n = 13 := by
  have h1 : n ≤ 13 := by
    by_contra h
    push_neg at h
    have h2 : n ≥ 14 := by
      omega
    have h3 : n ^ n ≥ 14 ^ 14 := by
      have h4 : n ≥ 14 := h2
      have h5 : n ^ n ≥ n ^ 14 := by
        have h6 : n ≥ 14 := h4
        have h7 : n ^ n ≥ n ^ 14 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals
          omega
        linarith
      have h8 : n ^ 14 ≥ 14 ^ 14 := by
        have h9 : n ≥ 14 := h4
        have h10 : n ^ 14 ≥ 14 ^ 14 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals
          omega
        linarith
      linarith [h5, h8]
    have h4 : (14 : ℕ) ^ 14 > 302875106592253 := by
      norm_num
    have h5 : n ^ n > 302875106592253 := by
      linarith [h3, h4]
    linarith [hn, h5]
  have h6 : n ≥ 13 := by
    by_contra h
    push_neg at h
    have h7 : n ≤ 12 := by
      omega
    have h8 : n ^ n ≤ 12 ^ 12 := by
      have h9 : n ≤ 12 := h7
      have h10 : n ^ n ≤ 12 ^ 12 := by
        have h11 : n ≤ 12 := h9
        have h12 : n ^ n ≤ 12 ^ n := by
          apply Nat.pow_le_pow_of_le_left
          all_goals
          omega
        have h13 : 12 ^ n ≤ 12 ^ 12 := by
          have h14 : n ≤ 12 := h11
          apply Nat.pow_le_pow_of_le_right
          all_goals
          omega
        linarith [h12, h13]
      linarith
    have h4 : (12 : ℕ) ^ 12 < 302875106592253 := by
      norm_num
    have h14 : n ^ n < 302875106592253 := by
      linarith [h8, h4]
    linarith [hn, h14]
  have h7 : n = 13 := by
    linarith [h1, h6]
  exact h7