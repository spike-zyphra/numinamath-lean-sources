import Mathlib

theorem algebra_10892 : {p : Equiv.Perm (Fin 4) | p 3 = 3}.encard = 6 := by
  rw [Set.encard]
  simp [Set.ncard_eq_toFinset_card']
  <;> native_decide