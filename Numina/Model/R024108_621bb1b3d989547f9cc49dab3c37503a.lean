import Mathlib

theorem number_theory_289729 :
    IsLeast {n | 0 < n ∧ (n % 2 = 0) ∧ (n % 4 = 0) ∧ (n % 6 = 0) ∧ (n % 8 = 0) ∧ (n % 10 = 0) ∧ (n % 12 = 0) ∧ (n % 14 = 0) ∧ (n % 16 = 0) ∧ (n % 18 = 0) ∧ (n % 20 = 0)} 5040 := by
  constructor
  · -- Show that 5040 is in the set.
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
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
  · -- Show no smaller positive integer is in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_2, hn_4, hn_6, hn_8, hn_10, hn_12, hn_14, hn_16, hn_18, hn_20⟩
    by_contra h
    push_neg at h
    interval_cases n <;> omega