import Mathlib

theorem number_theory_23312 :
    IsLeast {n : ℕ | 0 < n ∧ n ≠ 1 ∧ ∃ k, k^3 = n ∧ ∃ m, m^4 = n} 4096 := by
  constructor
  · -- Show that 4096 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    use 16
    constructor
    · norm_num
    use 8
    all_goals norm_num
  · -- Show that 4096 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, hn_ne, k, hk1, m, hm1⟩
    by_contra h
    push_neg at h
    have h1 : k^3 < 4096 := by
      linarith [hk1, h]
    have h2 : m^4 < 4096 := by
      linarith [hm1, h]
    have h3 : k < 16 := by
      by_contra h4
      push_neg at h4
      have h5 : k ≥ 16 := by omega
      have h6 : k^3 ≥ 16^3 := by
        have h7 : k ≥ 16 := by omega
        have h8 : k^3 ≥ 16^3 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals linarith
        linarith
      norm_num at h6
      all_goals linarith [h6, h1]
    have h7 : m < 8 := by
      by_contra h8
      push_neg at h8
      have h8 : m ≥ 8 := by omega
      have h9 : m^4 ≥ 8^4 := by
        have h9 : m ≥ 8 := by omega
        have h10 : m^4 ≥ 8^4 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals linarith
        linarith
      norm_num at h9
      all_goals linarith [h9, h2]
    interval_cases k <;> interval_cases m <;> omega