import Mathlib

theorem number_theory_307702 : {f : Fin 4 → Fin 4 | f.Injective}.ncard = 24 := by
  rw [Set.ncard_eq_toFinset_card']
  simp
  native_decide