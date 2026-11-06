import Mathlib

theorem algebra_10758 : Nat.card (Fin 4 → Fin 7) = 2401 := by
  simp [Nat.card_fun]
  <;> rfl