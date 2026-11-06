import Mathlib

theorem number_theory_611465 :
    IsLeast {n : ℕ | 0 < n ∧ 7 ∈ Nat.digits 10 (n ^ 2) ∧ 7 ∈ Nat.digits 10 ((n + 1) ^ 2) ∧ 7 ∉ Nat.digits 10 ((n + 2) ^ 2)} 27 := by
  constructor
  · -- Show 27 is in the set.
    constructor
    · norm_num
    constructor
    · native_decide
    constructor
    · native_decide
    · native_decide
  · -- Show no smaller element is in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn1, hn2, hn3⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn1 hn2 hn3 <;> all_goals norm_num at hn1 hn2 hn3 <;> all_goals tauto
  all_goals tauto