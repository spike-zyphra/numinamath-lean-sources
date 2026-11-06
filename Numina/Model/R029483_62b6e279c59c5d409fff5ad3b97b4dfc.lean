import Mathlib

theorem number_theory_19087 :
    IsLeast {n | 0 < n ∧ 365 ∣ 28 * n} 365 := by 
  constructor
  · -- Show 365 is in the set.
    constructor
    · norm_num
    · norm_num
  · -- Show there is no smaller element in the set.
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    have h1 : n < 365 := by linarith
    interval_cases n <;> omega