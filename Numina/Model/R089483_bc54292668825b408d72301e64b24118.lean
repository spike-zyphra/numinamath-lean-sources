import Mathlib

theorem number_theory_104978 : IsLeast {n | 0 < n ∧ 4 ∣ (n + 1) ∧ 6 ∣ (n + 1) ∧ 10 ∣ (n + 1) ∧ 12 ∣ (n + 1)} 59 := by
  constructor
  · -- Show that 59 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 59 is the smallest element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_4, hn_6, hn_10, hn_12⟩
    by_contra h
    push_neg at h
    have h1 : n < 59 := by linarith
    interval_cases n <;> omega