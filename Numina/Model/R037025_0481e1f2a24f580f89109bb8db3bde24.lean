import Mathlib

theorem number_theory_102217 :
    IsLeast {n | 0 < n ∧ ∃ k, k^2 = 2^8 + 2^11 + 2^n} 12 := by
  constructor
  · -- Show 12 in the set.
    constructor
    · norm_num
    · use 80
      all_goals norm_num
  · -- Show minimality.
    intro n hn
    rcases hn with ⟨hn_pos, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    have h1 : n < 12 := by linarith
    have h2 : k ≤ 80 := by
      by_contra h3
      push_neg at h3
      have h38 : k ≥ 81 := by linarith
      have h4 : k ^ 2 = 2^8 + 2^11 + 2^n := by linarith [hk]
      have h4a : k ^ 2 ≥ 81 ^ 2 := by
        nlinarith
      have h5 : n ≤ 11 := by omega
      have h6 : k ^ 2 ≤ 4352 := by 
        have h7 : n ≤ 11 := by omega
        have h8 : 2^n ≤ 2048 := by
          have h9 : n ≤ 11 := by omega
          have h10 : 2^n ≤ 2^11 := by
            apply pow_le_pow_right 
            all_goals linarith 
          have h11 : 2^11 = 2048 := by norm_num 
          linarith [h11]
        nlinarith [show k ^ 2 = 2^8 + 2^11 + 2^n from by linarith [hk]]
      nlinarith
    interval_cases n <;> try { 
      have h3 : k ≤ 80 := h2
      interval_cases k <;> omega 
    }