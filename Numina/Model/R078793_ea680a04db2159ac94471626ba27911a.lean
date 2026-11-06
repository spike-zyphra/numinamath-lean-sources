import Mathlib

theorem algebra_20052 : IsLeast {n | 0 < n ∧ 16 ∣ n ∧ 15 ∣ n ∧ 12 ∣ n} 240 := by
  constructor
  · -- Show 240 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show no smaller positive integer is in the set
    intro n hn
    rcases hn with ⟨hn_pos, h16, h15, h12⟩
    by_contra h
    push_neg at h
    interval_cases n <;> omega