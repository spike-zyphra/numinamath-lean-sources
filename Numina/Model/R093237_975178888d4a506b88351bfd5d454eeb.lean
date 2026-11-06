import Mathlib

theorem number_theory_255447 :
    IsLeast {n | 1 < n ∧ 2022 ∣ (n ^ 7 - 1)} 79 := by
  constructor
  · constructor
    · -- Show that 1 < 79
      norm_num 
    · -- Show that 2022 divides 79^7 - 1
      norm_num 
  · -- Show that 79 is the smallest element in the set
    intro n hn
    rcases hn with ⟨hn1, h2022⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h2022 hn1 <;> omega