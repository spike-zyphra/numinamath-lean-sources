import Mathlib

theorem number_theory_23243 : IsLeast {n  > 0 | (n * 697) % 12 = 0} 12 := by 
  constructor
  · -- Show 12 is in the set.
    constructor
    · -- Show 12 > 0.
      norm_num
    · -- Show (12 * 697) % 12 = 0.
      norm_num 
  · -- Show 12 is the least element in the set.
    intro n hn
    rcases hn with ⟨hn_pos, hn_mod⟩
    by_contra h
    push_neg at h 
    interval_cases n <;> norm_num at hn_mod <;> omega