import Mathlib

theorem number_theory_192496 : IsLeast {p | 10 < p ∧ (2 ^ p) % 1000 = 24} 110 := by
  constructor
  · -- Show that 110 is in the set
    constructor
    · -- Show that 10 < 110
      norm_num
    · -- Show that 2 ^ 110 % 1000 = 24
      norm_num
  · -- Show that 110 is the smallest
    intro p hp
    rcases hp with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at h2
    <;> omega