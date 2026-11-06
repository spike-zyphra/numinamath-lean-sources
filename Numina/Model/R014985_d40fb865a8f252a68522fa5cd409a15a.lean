import Mathlib

theorem number_theory_246731 :
    IsLeast {n : ℕ | 0 < n ∧ ∃ k, 3 * n + 1 = k ^ 2 ∧ ∃ m, 5 * n + 1 = m ^ 2} 16 := by 
  constructor
  · -- Show 16 is in the set
    constructor
    · norm_num
    · use 7
      constructor
      · norm_num
      · use 9
        all_goals norm_num
  · -- Show no smaller element is in the set
    intro n hn
    rcases hn with ⟨hn_pos, k, hk1, m, hm1⟩
    by_contra h
    push_neg at h
    have h1 : n < 16 := h
    interval_cases n <;> try { 
      norm_num at hk1 hm1 
      try { 
        have : k ≤ 12 := by nlinarith 
        interval_cases k <;> try { 
          omega 
        } 
      } 
      try { 
        have : m ≤ 20 := by nlinarith 
        interval_cases m <;> try { 
          omega 
        } 
      }
    }