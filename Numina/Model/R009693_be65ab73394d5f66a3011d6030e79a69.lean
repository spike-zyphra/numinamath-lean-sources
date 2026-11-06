import Mathlib

theorem number_theory_95385 :
IsLeast {n : ℕ | 0 < n ∧ (n^3) % 1000 = 888} 192 := by
  constructor
  · -- Show that 192 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show that 192 is the smallest element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_cube⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_cube <;> omega