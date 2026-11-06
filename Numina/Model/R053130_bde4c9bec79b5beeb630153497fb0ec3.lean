import Mathlib

theorem inequalities_6613 : {x : ℤ | -108 ≤ 15 * x + 9 ∧ 15 * x + 9 ≤ 65 ∧ x ≤ 0}.encard = 8 := by
  have h1 : {x : ℤ | -108 ≤ 15 * x + 9 ∧ 15 * x + 9 ≤ 65 ∧ x ≤ 0} = {-7, -6, -5, -4, -3, -2, -1, 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Proof that if x is in the set of integer solutions, it's in the singleton set
      intro h
      rcases h with ⟨h1, h2, h3⟩
      omega
    · -- Proof that if x is in the singleton set, it's in the integer solutions set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        omega
  rw [h1]
  rw [Set.encard]
  simp
  <;> rfl