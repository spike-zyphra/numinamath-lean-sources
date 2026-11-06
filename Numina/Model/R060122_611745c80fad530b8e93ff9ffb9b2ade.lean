import Mathlib

theorem number_theory_99419 : IsLeast {n | 0 < n ∧ (n ^ 3) % 1000 = 888} 192 := by
  constructor 
  · -- Show 192 is in the set
    constructor
    · -- Show 0 < 192
      norm_num 
    · -- Show 192^3 % 1000 = 888
      norm_num 
  · -- Show that 192 is the least 
    intro n hn
    rcases hn with ⟨hn_pos, hn_cube⟩

    by_contra h
    push_neg at h 
    have h' : n < 192 := h 
    interval_cases n <;> norm_num at hn_cube <;> all_goals omega