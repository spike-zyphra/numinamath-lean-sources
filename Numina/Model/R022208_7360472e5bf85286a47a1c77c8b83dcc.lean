import Mathlib

theorem inequalities_5610 :
    Set.ncard {x : ℤ | -15 ≤ 4 * x - 9 ∧ 4 * x - 9 ≤ 35} = 13 := by
  have h1 : {x : ℤ | -15 ≤ 4 * x - 9 ∧ 4 * x - 9 ≤ 35} = Set.Icc (-1 : ℤ) 11 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- First, prove the set {x : ℤ | -15 ≤ 4 * x - 9 ∧ 4 * x - 9 ≤ 35} ⊆ Set.Icc (-1 : ℤ) 11
      rintro ⟨h1, h2⟩
      constructor
      · -- Show x ≥ -1
        omega
      · -- Show x ≤ 11
        omega
    · -- Now prove the reverse: Set.Icc (-1 : ℤ) 11 ⊆ {x : ℤ | -15 ≤ 4 * x - 9 ∧ 4 * x - 9 ≤ 35}
      rintro ⟨h1, h2⟩
      constructor
      · -- Show -15 ≤ 4 * x - 9
        omega
      · -- Show 4 * x - 9 ≤ 35
        omega
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }