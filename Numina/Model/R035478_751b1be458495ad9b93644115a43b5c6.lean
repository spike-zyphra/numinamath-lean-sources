import Mathlib

theorem number_theory_191927 :
    IsLeast {n | 0 < n ∧ (∃ k, k^2 = 4 * n + 1) ∧ ∃ m, m^2 = 6 * n + 1} 20 := by
  constructor
  · -- Show 20 is in the set
    constructor
    · norm_num
    constructor
    · -- Show that there exists k such that k^2 = 4 * 20 + 1 = 81
      use 9
      all_goals norm_num
    · -- Show that there exists m such that m^2 = 6 * 20 + 1 = 121
      use 11
      all_goals norm_num
  · -- Show that no integer less than 20 is in the set
    intro n hn
    rcases hn with ⟨hn_pos, ⟨k, hk⟩, ⟨m, hm⟩⟩
    by_contra h
    push_neg at h
    have h1 : n < 20 := h
    have h2 : k ≤ 44 := by
      nlinarith
    have h3 : m ≤ 62 := by
      nlinarith
    interval_cases n <;> try { 
      norm_num at hk hm
      all_goals
        try { 
          interval_cases k <;> try { 
            omega
          }
        }
        <;> try { 
          interval_cases m <;> try { 
            omega
          }
        }
    }