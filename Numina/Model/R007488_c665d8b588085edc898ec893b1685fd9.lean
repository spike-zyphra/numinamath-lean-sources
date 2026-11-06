import Mathlib

theorem algebra_12238 : Nat.card (Fin 3 → Fin 7) = 343 := by
  simp [Nat.card_fun]