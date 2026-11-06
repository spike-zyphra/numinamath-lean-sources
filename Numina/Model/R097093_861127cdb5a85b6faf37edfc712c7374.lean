import Mathlib

theorem number_theory_153241 (n : ℕ) :
    IsLeast {n | 0 < n ∧ (107 * n) % 100 = n % 100} 50 := by
  constructor
  · -- Show 50 is in the set
    constructor
    · -- Show 50 > 0
      norm_num
    · -- Show 107 * 50 % 100 = 50 % 100
      norm_num
  · -- Show there is no smaller element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_cong⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_cong <;> omega