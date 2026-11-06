import Mathlib

theorem number_theory_62552 : IsLeast {n | 0 < n ∧ (2013 ^ n) % 1000 = 1} 100 := by
  constructor
  · -- Show that 100 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show that 100 is the smallest in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_eq⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_eq