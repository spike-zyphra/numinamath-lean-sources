import Mathlib

theorem algebra_11340 : Set.ncard {((x1, y1), (x2, y2)) : (Fin 4 × Fin 4) × (Fin 4 × Fin 4) | x1 < x2 ∧ y1 < y2} = 36 := by 
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.filter]
  <;> native_decide