import Mathlib

theorem algebra_16184 : Set.ncard {(x, y) : Fin 6 × Fin 6 | x < y ∧ x ≠ y + 1 ∧ x ≠ y - 1} = 9 := by
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.filter]
  <;> try { native_decide }
  <;> try { rfl }