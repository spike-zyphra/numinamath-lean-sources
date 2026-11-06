import Mathlib

theorem number_theory_47233 : IsGreatest {n : ℤ | n < 103 ∧ 103 ∣ n ^ 3 - 1} 56 := by
  constructor
  · -- Show that 56 is in the set.
    constructor
    · norm_num
    · norm_num
  · -- Show that 56 is greatest in the set.
    intro n hn
    rcases hn with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : n ≤ 102 := by
      omega
    interval_cases n <;> norm_num at h2 <;> omega