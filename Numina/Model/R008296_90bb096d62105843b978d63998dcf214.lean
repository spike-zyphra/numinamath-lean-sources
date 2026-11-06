import Mathlib

theorem algebra_11931 : Set.ncard {a : Fin 4 → Fin 26 | a 0 = a 3} = 17576 := by
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> native_decide