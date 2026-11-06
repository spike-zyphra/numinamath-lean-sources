import Mathlib

theorem number_theory_173141 : IsLeast {n | 0 < n ∧ n % 5 = 2 ∧ n % 7 = 3 ∧ n % 9 = 4} 157 := by
  constructor
  · -- Show 157 in the set
    show 0 < 157 ∧ 157 % 5 = 2 ∧ 157 % 7 = 3 ∧ 157 % 9 = 4
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show 157 is the least
    intro n hn
    rcases hn with ⟨hn_pos, hn_mod5, hn_mod7, hn_mod9⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_mod5 hn_mod7 hn_mod9 <;> omega