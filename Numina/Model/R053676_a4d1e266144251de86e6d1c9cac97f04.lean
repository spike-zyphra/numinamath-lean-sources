import Mathlib

theorem number_theory_26731 :
    IsLeast {n : ℕ | 0 < n ∧ (315^3 - n^3) % (315^2 - n^2) = 0} 90 := by
  constructor
  · constructor
    · norm_num -- Show 0 < 90
    · norm_num -- Show (315^3 - 90^3) % (315^2 - 90^2) = 0
  · intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_div <;> omega