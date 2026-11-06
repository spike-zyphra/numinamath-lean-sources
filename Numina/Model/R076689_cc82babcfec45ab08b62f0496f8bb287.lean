import Mathlib

theorem number_theory_171436 :
    IsLeast {n : ℕ | 0 < n ∧ ¬∃ k l, k + l = n ∧ Nat.digits 10 k = List.reverse (Nat.digits 10 k) ∧
      Nat.digits 10 l = List.reverse (Nat.digits 10 l)} 21 := by
  constructor
  · -- Show 21 is in the set.
    constructor
    · norm_num
    · -- Assume for contradiction that 21 can be written as the sum of two palindromes
      intro h
      rcases h with ⟨k, l, hk, hk_pal, hl_pal⟩
      have h1 : k ≤ 21 := by omega
      have h2 : l ≤ 21 := by omega
      interval_cases k <;> interval_cases l <;> norm_num at hk hk_pal hl_pal <;> try { all_goals contradiction }
  · -- Now prove minimality
    intro n hn
    rcases hn with ⟨hn_pos, hn_not_sum⟩
    by_contra h
    push_neg at h
    have h1 : n < 21 := by linarith
    have h2 : ∃ k l, k + l = n ∧ Nat.digits 10 k = List.reverse (Nat.digits 10 k) ∧ Nat.digits 10 l = List.reverse (Nat.digits 10 l) := by
      interval_cases n <;> try { 
        use 0, 1
        all_goals native_decide 
      } <;> try { 
        use 1, 0 
        all_goals native_decide 
      } <;> try { 
        use 2, 0 
        all_goals native_decide 
      } <;> try { 
        use 3, 0 
        all_goals native_decide 
      } <;> try { 
        use 4, 0 
        all_goals native_decide 
      } <;> try { 
        use 5, 0 
        all_goals native_decide 
      } <;> try { 
        use 6, 0 
        all_goals native_decide 
      } <;> try { 
        use 7, 0 
        all_goals native_decide 
      } <;> try { 
        use 8, 0 
        all_goals native_decide 
      } <;> try { 
        use 9, 0 
        all_goals native_decide 
      } <;> try { 
        use 9, 1 
        all_goals native_decide 
      } <;> try { 
        use 11, 0 
        all_goals native_decide 
      } <;> try { 
        use 11, 1 
        all_goals native_decide 
      } <;> try { 
        use 9, 4 
        all_goals native_decide 
      } <;> try { 
        use 9, 5 
        all_goals native_decide 
      } <;> try { 
        use 9, 6 
        all_goals native_decide 
      } <;> try { 
        use 9, 7 
        all_goals native_decide 
      } <;> try { 
        use 9, 8 
        all_goals native_decide 
      } <;> try { 
        use 9, 9 
        all_goals native_decide 
      } <;> try { 
        use 11, 8 
        all_goals native_decide 
      } <;> try { 
        use 9, 11 
        all_goals native_decide 
      }
    have h3 := hn_not_sum h2
    contradiction