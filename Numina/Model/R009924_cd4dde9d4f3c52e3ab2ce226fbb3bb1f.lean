import Mathlib

theorem algebra_17137 (n : ℕ) (hn : n = 24 / 2) :
    Set.ncard {f : Fin 4 → Fin n | f.Injective} = 11880 := by 
  rw [hn]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> native_decide