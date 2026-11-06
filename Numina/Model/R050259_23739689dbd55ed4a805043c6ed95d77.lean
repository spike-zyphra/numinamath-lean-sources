import Mathlib

theorem number_theory_12471 : IsLeast {n | 0 < n ∧ 3 ∣ 412 + n} 2 := by 
  constructor 
  · -- Show that 2 is indeed in the set.
    constructor 
    · norm_num 
    · norm_num 
  · -- Show that 2 is the smallest element in the set.
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    omega