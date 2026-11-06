import Mathlib

theorem number_theory_129916 : IsLeast {n | n > 38 ∧ (n ^ 2) % 1000 = 444} 462 := by
  constructor
  · -- Show 462 is in the set
    refine' ⟨by norm_num, by norm_num⟩
  · -- Show 462 is the smallest such number
    intro n hn
    have ⟨hn1, hn2⟩ := hn
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn1 hn2 <;> omega