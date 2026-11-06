import Mathlib

theorem number_theory_277948 : IsGreatest {x | 4 ∣ x ∧ x < 100} 96 := by
  constructor
  · -- Show that 96 is in the set
    constructor
    · -- Show that 4 divides 96
      norm_num
    · -- Show that 96 < 100
      norm_num
  · -- Show that any element in the set is less than or equal to 96
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    omega