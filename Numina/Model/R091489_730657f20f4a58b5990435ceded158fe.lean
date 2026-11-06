import Mathlib

theorem number_theory_152008 :
    IsLeast {n | 0 < n ∧ ∃ k, n = 2 * k ^ 2 ∧ ∃ m, n = 3 * m ^ 3} 648 := by
  constructor
  · -- Let's prove that 648 is in the set
    constructor
    · -- Show 648 is positive
      norm_num
    · -- Show existence of k
      use 18
      constructor
      · -- Show n = 2 * k^2
        norm_num
      · -- Show existence of m
        use 6
        all_goals norm_num
  · -- Let's prove that 648 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, k, hk_sq, m, hm_cube⟩
    by_contra h
    push_neg at h
    have h1 : n < 648 := h
    have h2 : m ^ 3 < 216 := by
      nlinarith [hm_cube, h1]
    have h3 : m ≤ 5 := by
      by_contra h
      push_neg at h
      have h4 : m ≥ 6 := by omega
      have h5 : m ^ 3 ≥ 216 := by
        have h6 : m ^ 3 ≥ 6 ^ 3 := by
          apply pow_le_pow_left
          all_goals omega
        nlinarith [h6]
      nlinarith [h2, h5]
    have h4 : k ^ 2 < 324 := by
      nlinarith [hk_sq, h1]
    have h5 : k ≤ 17 := by
      nlinarith [h4]
    interval_cases m <;> try { 
      norm_num [hm_cube] at *
      all_goals
      interval_cases k <;> omega
    }