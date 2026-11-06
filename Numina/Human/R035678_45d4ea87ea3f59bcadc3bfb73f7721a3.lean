import Mathlib

theorem algebra_16093 : Set.ncard {x : Fin 3 → Fin 5 | x.Injective} = 60 := by
  rw [Set.ncard_eq_toFinset_card]
  simp
  native_decide