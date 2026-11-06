import Mathlib

theorem inequalities_5015 : Set.ncard {x : ℤ | -21 ≤ 3 * x + 5 ∧ 3 * x + 5 ≤ 38} = 20 := by
  have h1 : {x : ℤ | -21 ≤ 3 * x + 5 ∧ 3 * x + 5 ≤ 38} = Set.Icc (-8) 11 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Show that if (-21 ≤ 3 * x + 5 ∧ 3 * x + 5 ≤ 38), then x ∈ Set.Icc (-8) 11
      intro h
      rcases h with ⟨h1, h2⟩
      constructor
      · -- Show that x ≥ -8
        omega
      · -- Show that x ≤ 11
        omega
    · -- Show that if x ∈ Set.Icc (-8) 11, then (-21 ≤ 3 * x + 5 ∧ 3 * x + 5 ≤ 38)
      rintro ⟨h1, h2⟩
      constructor
      · -- Show that -21 ≤ 3 * x + 5
        omega
      · -- Show that 3 * x + 5 ≤ 38
        omega
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> native_decide