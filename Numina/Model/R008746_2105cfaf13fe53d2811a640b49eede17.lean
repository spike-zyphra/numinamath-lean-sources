import Mathlib

theorem algebra_15925 : Set.ncard {(x, y) : Fin 7 × Fin 7 | x < y ∧ x ≠ y - 1 ∧ x ≠ y + 1} = 14 := by
  simp [Set.ncard_eq_toFinset_card']
  <;> native_decide