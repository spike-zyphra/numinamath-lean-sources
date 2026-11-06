import Mathlib

theorem algebra_11701 : Nat.card (Fin 4 → Fin 11) = 14641 := by 
  simp
  <;> try native_decide