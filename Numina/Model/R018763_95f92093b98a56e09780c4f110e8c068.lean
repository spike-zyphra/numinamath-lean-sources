import Mathlib

theorem number_theory_162365 (p : ℕ) :
    Nat.Prime (p ^ p + 1) ∧ (Nat.digits 10 (p ^ p + 1)).length ≤ 19 ↔
    p ^ p + 1 = 2 ∨ p ^ p + 1 = 5 ∨ p ^ p + 1 = 257 := by
  constructor
  · -- Assume Nat.Prime (p ^ p + 1) ∧ (Nat.digits 10 (p ^ p + 1)).length ≤ 19, prove p ^ p + 1 = 2 ∨ p ^ p + 1 = 5 ∨ p ^ p + 1 = 257
    intro h
    rcases h with ⟨h_prime, h_digit⟩
    by_cases hp1 : p > 16
    · -- p > 16
      -- p^p + 1 has more than 19 digits
      have h2 : (p ^ p + 1) ≥ (17 ^ 17 + 1) := by
        have h3 : p ≥ 17 := by omega
        have h4 : p ^ p ≥ 17 ^ 17 := by
          have h5 : p ≥ 17 := h3
          have h7 : p ≥ 17 := by omega
          have h8 : p ^ p ≥ 17 ^ 17 := by
            have h7 : p ≥ 17 := by omega 
            have h8 : p ^ p ≥ 17 ^ p := by 
              apply Nat.pow_le_pow_of_le_left 
              all_goals linarith 
            have h9 : 17 ^ p ≥ 17 ^ 17 := by 
              apply Nat.pow_le_pow_right 
              all_goals linarith 
            linarith 
          linarith 
        linarith
      have h3 : (Nat.digits 10 (p ^ p + 1)).length > 19 := by 
        have h4 : p ≥ 17 := by omega 
        have h6 : (p ^ p + 1) ≥ 17 ^ 17 + 1 := h2
        have h7 : (Nat.digits 10 (p ^ p + 1)).length ≥ (Nat.digits 10 (17 ^ 17 + 1)).length := by 
          apply Nat.le_digits_len_le 
          all_goals linarith 
        have h6 : (Nat.digits 10 (17 ^ 17 + 1)).length ≥ 20 := by 
          norm_num 
        linarith 
      linarith
    · -- p ≤ 16 
      -- Let p be bounded 
      have hp16 : p ≤ 16 := by omega 
      interval_cases p <;> norm_num at h_prime h_digit ⊢ 
      <;> tauto 
  · -- Assume the RHS, prove the LHS
    rintro (h | h | h)
    · -- Case p ^ p + 1 = 2 
      rw [h]
      constructor
      · norm_num
      · norm_num
    · -- Case p ^ p + 1 = 5 
      rw [h]
      constructor
      · norm_num 
      · norm_num 
    · -- Case p ^ p + 1 = 257 
      rw [h]
      constructor 
      · norm_num 
      · norm_num