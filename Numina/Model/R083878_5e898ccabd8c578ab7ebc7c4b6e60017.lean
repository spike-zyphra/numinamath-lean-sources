import Mathlib

theorem number_theory_82581 :
    IsLeast {n : ℕ | 0 < n ∧ (25 ^ n + 16 ^ n) % 121 = 1} 32 := by
  constructor
  · -- Show that 32 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show that for all n in the set, 32 ≤ n
    intro n hn
    rcases hn with ⟨hn_pos, hn_cong⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_cong <;> omega