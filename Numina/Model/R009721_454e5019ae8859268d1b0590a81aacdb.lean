import Mathlib

theorem algebra_13038 : Set.ncard {f : Fin 4 → Fin 5 | Function.Injective f} = 120 := by
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> native_decide