import Mathlib

theorem number_theory_11093 :
    IsLeast {n | 0 < n ∧ (n % 10 = 9) ∧ (7 ∣ n)} 49 := by 
  constructor 
  · -- Show that 49 is in the set.
    constructor
    · norm_num  -- Show that 49 is positive
    constructor
    · norm_num -- Show that 49 ends with 9
    · norm_num -- Show that 49 is divisible by 7
  · -- Show that for all n in the set, 49 ≤ n 
    intro n hn 
    rcases hn with ⟨hn_pos, hn_mod, hn_div⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_pos hn_mod hn_div <;> omega
    all_goals 
      omega