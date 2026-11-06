import Mathlib

set_option maxHeartbeats 10000000

theorem number_theory_205510 : IsLeast {n | 0 < n ∧ (Nat.digits 10 (2007 * n)).take 3 = [7, 3, 8]} 691 := by 
  constructor
  · -- Show that 691 is in the set
    constructor
    · -- Show 691 > 0
      norm_num
    · -- Show the last three digits of 2007 * 691 are 7, 3, 8
      norm_num
  · -- Show no smaller positive integer is in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_digits⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_digits <;> all_goals norm_num at hn_pos hn_digits <;> try { contradiction }