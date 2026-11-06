import Mathlib

theorem number_theory_301106 : IsLeast {n | 0 < n ∧ 1 < n ∧ 2016 ∣ 3 * n ^ 3 + 2013} 193 := by
  constructor
  · -- Show 193 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show there is no smaller element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_gt, hn_div⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_div <;> omega