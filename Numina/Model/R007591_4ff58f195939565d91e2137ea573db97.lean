import Mathlib

theorem algebra_14092 : Fintype.card (Fin 5 → Fin 5) = 3125 := by 
  simp [Fintype.card_fun]
  <;> try native_decide