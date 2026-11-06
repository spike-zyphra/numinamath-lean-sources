import Mathlib

theorem number_theory_19516 : IsLeast {n | n > 3456 ∧ (Nat.digits 10 n).sum = 12} 3504 := by
  constructor
  · -- Show that 3504 is in the set.
    constructor
    · -- Verify 3504 > 3456
      norm_num
    · -- Verify sum of digits of 3504 is 12
      norm_num
  · -- Show that 3504 is the smallest.
    intro n hn
    rcases hn with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h1 h2 <;> all_goals
      contradiction