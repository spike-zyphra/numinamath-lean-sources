import Mathlib

theorem algebra_15464 : Fintype.card (Fin 2 → Fin 10) = 100 := by 
  simp [Fintype.card_fun]
  <;> native_decide