import Mathlib

theorem number_theory_11804 :
    IsLeast {n | 0 < n ∧ n ≥ 1000 ∧ (n % 2 = 0 ∧ n % 3 = 0 ∧ n % 5 = 0 ∧ n % 7 = 0)} 1050 := by 
  constructor 
  · constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 1050 is the smallest in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_4, ⟨h2, h3, h5, h7⟩⟩
    by_contra h
    push_neg at h
    interval_cases n <;> omega