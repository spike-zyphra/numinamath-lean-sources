import Mathlib

theorem number_theory_6915 : IsLeast {x | x > 0 ∧ x % 225 = 0 ∧ x % 365 = 0} 16425 := by
  constructor
  · -- Show that 16425 is in the set.
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 16425 is minimal
    intro x h
    rcases h with ⟨hx1, hx2, hx3⟩
    by_contra h'
    push_neg at h'
    have h1 : x < 16425 := by linarith
    omega