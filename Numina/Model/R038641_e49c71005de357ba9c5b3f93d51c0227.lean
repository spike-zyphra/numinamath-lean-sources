import Mathlib

theorem algebra_110634 (a : Fin 8 → ℝ) (ha : ∀ i, a i ≠ 0) :
    ∃ x, x ≥ 0 ∧ x = a 0 * a 2 + a 1 * a 3 ∨
          x = a 0 * a 4 + a 1 * a 5 ∨
          x = a 0 * a 6 + a 1 * a 7 ∨
          x = a 2 * a 4 + a 3 * a 5 ∨
          x = a 2 * a 6 + a 3 * a 7 ∨
          x = a 4 * a 6 + a 5 * a 7 := by

  use (a 0 * a 4 + a 1 * a 5)
  simp