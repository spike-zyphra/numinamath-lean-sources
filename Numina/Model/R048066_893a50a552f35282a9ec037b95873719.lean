import Mathlib

theorem number_theory_317426 (m n : ℕ) (h : m^m + (m * n)^n = 1984) :
    m = 4 ∧ n = 3 := by
  have h1 : m ≤ 12 := by
    by_contra h1
    push_neg at h1
    have h2 : m ^ m ≥ 13 ^ 13 := by
      have h3 : m ≥ 13 := by linarith
      have h4 : m ^ m ≥ 13 ^ 13 := by
        have h5 : m ≥ 13 := h3
        have h6 : m ≥ 13 := h3
        have h7 : m ^ m ≥ 13 ^ m := by
          apply Nat.pow_le_pow_of_le_left
          all_goals linarith
        have h8 : 13 ^ m ≥ 13 ^ 13 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals linarith
        have h9 : m ^ m ≥ 13 ^ 13 := by
          nlinarith [h7, h8]
        linarith
      linarith
    have h10 : 13 ^ 13 > 1984 := by norm_num
    have h11 : m ^ m + (m * n) ^ n ≥ 13 ^ 13 := by
      linarith [show m ^ m ≥ 0 by positivity, show (m * n) ^ n ≥ 0 by positivity]
    nlinarith
  have h2 : n ≤ 12 := by
    by_contra h2
    push_neg at h2
    have h13 : n ≥ 13 := by linarith
    by_cases hm : m > 0
    · -- Case where m > 0
      have h8 : (m * n) ^ n ≥ 13 ^ 13 := by
        have h9 : m * n ≥ 13 := by
          nlinarith [show m ≥ 1 by omega, show n ≥ 13 by linarith]
        have h10 : n ≥ 13 := by linarith
        have h13 : (m * n) ^ n ≥ 13 ^ 13 := by
          have h14 : m * n ≥ 13 := h9
          have h15 : n ≥ 13 := h10
          have h16 : ( (m * n) ^ n ) ≥ ( 13 ^ 13 ) := by
            have h17 : m * n ≥ 13 := h9
            have h18 : (m * n) ^ n ≥ 13 ^ n := by
              apply Nat.pow_le_pow_of_le_left 
              all_goals 
                nlinarith
            have h19 : 13 ^ n ≥ 13 ^ 13 := by
              apply Nat.pow_le_pow_of_le_right 
              all_goals 
                omega
            have h20 : (m * n) ^ n ≥ 13 ^ 13 := by
              nlinarith
            linarith
          linarith
        linarith
      have h9 : 13 ^ 13 > 1984 := by norm_num
      have h10 : m ^ m + (m * n) ^ n ≥ 13 ^ 13 := by
        have h51 : m ^ m ≥ 0 := by positivity
        have h52 : (m * n) ^ n ≥ 0 := by positivity
        linarith [h51, h8, h52]
      nlinarith
    · -- Case where m ≤ 0, so m = 0.
      have h11 : m = 0 := by linarith
      rw [h11] at h
      have h6 : (0 : ℕ) ^ (0 : ℕ) + ( (0 : ℕ) * n ) ^ n = 1 := by
        have h1 : (0 : ℕ) ^ (0 : ℕ) = 1 := by 
          simp 
        have h2 : ( (0 : ℕ) * n ) ^ n = 0 := by 
          have h3 : ( (0 : ℕ) * n ) = 0 := by 
            simp 
          rw [h3]
          have h4 : (0 : ℕ) ^ n = 0 := by
            have h5 : n ≥ 1 := by
              omega 
            have h6 : (0 : ℕ) ^ n = 0 := by
              apply zero_pow 
              all_goals 
                omega 
            linarith
          linarith
        linarith [h1, h2]
      nlinarith [h6]
  interval_cases m <;> try { 
    omega 
  } <;> try { 
    interval_cases n <;> omega 
  }