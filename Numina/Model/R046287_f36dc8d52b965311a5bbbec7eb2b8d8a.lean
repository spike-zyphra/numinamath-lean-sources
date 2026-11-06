import Mathlib

theorem number_theory_60088 :
    IsLeast {n : ℕ | 0 < n ∧ ∃ k, 9 * n = k^2 ∧ ∃ m, 12 * n = m^3} 144 := by
  constructor
  · -- Prove that 144 is in the least
    constructor
    · norm_num
    · -- Show existence of integers k and m such that
      use 36
      constructor
      · -- Show that 9 * 144 = 36^2
        norm_num
      · -- Show existence of integer m such that
        use 12
        all_goals norm_num
  · -- Prove that 144 is the least in the set
    intro n hn
    rcases hn with ⟨hn_pos, k, hk_sq, m, hm_cub⟩
    by_contra h
    push_neg at h
    have h1 : k^2 = 9 * n := by linarith
    have h2 : m^3 = 12 * n := by linarith
    have h3 : k < 36 := by nlinarith
    have h4 : m < 12 := by
      by_contra h6
      push_neg at h6
      have h7 : m^3 ≥ 12^3 := by
        have h8 : m ≥ 12 := by linarith [h6]
        have h9 : m^3 ≥ 12^3 := by
          apply Nat.pow_le_pow_of_le_left 
          all_goals linarith 
        linarith 
      nlinarith [h7, show 12 * n < 1728 by nlinarith, h2]
    interval_cases k <;> try { 
      omega 
    }
    <;> try { 
      interval_cases m <;> omega 
    }