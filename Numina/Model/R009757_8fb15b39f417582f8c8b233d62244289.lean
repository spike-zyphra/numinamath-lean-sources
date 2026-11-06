import Mathlib

theorem algebra_21655 :
    Set.encard {x : Fin 3 → Fin 26 | x 2 ≠ x 0 ∧ x 1 ∈ ({0, 4, 8, 14, 20} : Finset _)} = 3250 := by 
  rw [Set.encard]
  simp [Finset.card]
  <;> native_decide