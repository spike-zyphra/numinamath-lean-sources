import Mathlib
set_option maxHeartbeats 999999999
set_option maxRecDepth 999999999
theorem number_theory_96331 :
IsLeast {n | 0 < n ∧ (Nat.digits 10 n).sum = 20 ∧ (Nat.digits 10 (n + 864)).sum = 20} 695 := by
  constructor
  · -- Show that 695 is in the set
    constructor
    · norm_num -- Show 695 > 0
    constructor
    · norm_num -- Show digit sum of 695 is 20
    · norm_num -- Show digit sum of 695 + 864 is 20
  · -- Show that 695 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, hn_sum, hn_sum'⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_pos hn_sum hn_sum' <;> try { all_goals omega }