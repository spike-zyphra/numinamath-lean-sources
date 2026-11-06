import Mathlib

open Real

theorem inequalities_604065 (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ x y, x = a 0 ∧ y = a 1 ∨ x = a 1 ∧ y = a 2 ∨ x = a 2 ∧ y = a 0 ∧
    0 < (x - y) / (1 + x * y) ∧ (x - y) / (1 + x * y) ≤ 1 := by
  use a 0, a 1
  left
  constructor
  · rfl
  · rfl