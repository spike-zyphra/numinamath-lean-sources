import Mathlib

theorem number_theory_284909 : {x | x ∈ Finset.range 13 ∧ ¬(x % 2 = 0 ∨ x % 3 = 0)}.ncard = 4 := by
  have h1 : {x | x ∈ Finset.range 13 ∧ ¬(x % 2 = 0 ∨ x % 3 = 0)} = {1, 5, 7, 11} := by
    ext x
    simp only [Finset.mem_range, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Forward implication: if x ∈ the set then x ∈ {1,5,7,11}
      intro h
      rcases h with ⟨hx1, hx2⟩
      have hx3 : x < 13 := by
        omega
      interval_cases x <;> tauto
    · -- Backward implication: if x ∈ {1,5,7,11} then x ∈ the set
      rintro (rfl | rfl | rfl | rfl)
      · -- Case x = 1
        constructor
        · norm_num
        · norm_num
      · -- Case x = 5
        constructor
        · norm_num
        · norm_num
      · --  Case x = 7
        constructor
        · norm_num
        · norm_num
      · --  Case x = 11
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { tauto }