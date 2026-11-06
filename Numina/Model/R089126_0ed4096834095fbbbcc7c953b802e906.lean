import Mathlib

theorem number_theory_118845 :
    IsLeast {n | 0 < n ∧ 11 ∣ (n + 2013) ∧ 13 ∣ (n + 2013)} 132 := by
  constructor
  · -- Show 132 is in the set.
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show 132 is the least in the set.
    intro n hn
    rcases hn with ⟨hn_pos, hn_11, hn_13⟩
    omega