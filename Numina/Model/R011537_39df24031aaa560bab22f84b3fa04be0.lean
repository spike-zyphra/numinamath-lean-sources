import Mathlib

theorem number_theory_6202 :
    IsLeast {x : ℕ | x > 37 ∧ x^2 % 11 = 4} 42 := by
  constructor
  · -- Show that 42 is in the set.
    constructor
    · norm_num
    · norm_num
  · -- Show that 42 is minimal.
    intro x h
    rcases h with ⟨hx1, hx2⟩
    by_contra h'
    push_neg at h'
    have h3 : x < 42 := h'
    have h4 : x > 37 := hx1
    interval_cases x <;> norm_num at hx2 <;> omega