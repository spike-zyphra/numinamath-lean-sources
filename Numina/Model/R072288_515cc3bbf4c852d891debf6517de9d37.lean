import Mathlib

theorem inequalities_5314 : {x : ℤ | -7 ≤ (3 * x - 14) / 2 ∧ (3 * x - 14) / 2 ≤ 13}.encard = 14 := by
  have h1 : {x : ℤ | -7 ≤ (3 * x - 14) / 2 ∧ (3 * x - 14) / 2 ≤ 13} = Set.Icc 0 13 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Forward direction: inequality to [0,13]
      intro h
      rcases h with ⟨h1, h2⟩
      omega
    · -- Backward direction: [0,13] to inequality
      rintro ⟨h1, h2⟩
      omega
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_eq_toFinset_card']
  <;> rfl