import Mathlib

theorem number_theory_16226 :
    IsLeast {n | 0 < n ∧ n > 5 ∧ Nat.digits 2 n = List.reverse (Nat.digits 2 n) ∧
      Nat.digits 4 n = List.reverse (Nat.digits 4 n)} 15 := by 
  constructor
  · -- Show that 15 is indeed in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · native_decide
    · native_decide
  · -- Show that 15 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, hn_gt, hn_pal2, hn_pal4⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at *
    <;> all_goals contradiction
    all_goals
      all_goals contradiction