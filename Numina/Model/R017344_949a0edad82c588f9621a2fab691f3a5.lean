import Mathlib

theorem number_theory_13912 :
    IsLeast {n | 0 < n ∧ ∃ k, n = k^2 ∧ 2016 ∣ n} 28224 := by
  constructor
  · -- Show 28224 is in the set
    constructor
    · norm_num
    · use 168
      all_goals norm_num
  · -- Show 28224 is the smallest in the set
    intro n hn
    rcases hn with ⟨hn_pos, k, rfl, hk⟩
    by_contra h
    push_neg at h
    have h1 : k ≤ 167 := by
      nlinarith
    interval_cases k <;> norm_num at hk ⊢ <;> omega