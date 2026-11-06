import Mathlib

theorem inequalities_6166 : {x : ℤ | -5 ≤ ((x - 7) * 2 - 9) / 3 ∧ ((x - 7) * 2 - 9) / 3 < 3}.ncard = 12 := by 
  have h1 : {x : ℤ | -5 ≤ ((x - 7) * 2 - 9) / 3 ∧ ((x - 7) * 2 - 9) / 3 < 3} = Set.Icc 4 15 := by 
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Forward direction: prove inequality constraints imply 4 ≤ x ≤ 15
      intro h
      rcases h with ⟨h1, h2⟩
      omega
    · -- Backward direction: prove 4 ≤ x ≤ 15 implies inequality constraints
      rintro ⟨h1, h2⟩
      constructor <;> omega
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide