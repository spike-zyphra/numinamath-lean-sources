import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_14307 {r : ℝ} (hr : r = 2 / π) :
    2 * r * π = 4 := by
  rw [hr]
  field_simp [Real.pi_ne_zero]
  <;> ring