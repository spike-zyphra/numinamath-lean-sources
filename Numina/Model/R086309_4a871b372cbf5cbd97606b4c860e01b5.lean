import Mathlib

theorem number_theory_318935 :
    IsLeast {x | 1 < x ∧ x % 4 = 1 ∧ x % 5 = 1 ∧ x % 6 = 1} 61 := by
  constructor
  · -- First, show that 61 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Now, show that 61 is the smallest
    intro x hx
    rcases hx with ⟨hx1, h4, h5, h6⟩
    omega