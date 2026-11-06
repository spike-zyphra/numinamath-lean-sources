import Mathlib

theorem number_theory_10438 :
    IsLeast {n : ℕ | 0 < n ∧ ∃ k, k^2 = 3 * n + 1 ∧ ∃ m, m^2 = 5 * n + 1} 16 := by
  constructor
  · -- Show that 16 is in the set
    constructor
    · norm_num
    · use 7
      constructor
      · norm_num
      · use 9
        all_goals norm_num
  · -- Show that 16 is the least
    intro n hn
    rcases hn with ⟨hn_pos, k, hk, m, hm⟩
    by_contra h
    push_neg at h
    have h1 : k^2 = 3 * n + 1 := by linarith
    have h2 : m^2 = 5 * n + 1 := by linarith
    have h3 : k ≤ 12 := by nlinarith
    have h4 : m ≤ 17 := by nlinarith
    interval_cases k <;> try { 
      omega 
    }
    <;> interval_cases m <;> try { 
      omega 
    }
    <;> norm_num at h1 h2
    <;> try { 
      exfalso 
      <;> try { 
        nlinarith 
      } 
    }
    <;> try { 
      omega 
    }