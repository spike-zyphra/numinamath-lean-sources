import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_140450 {x : ℝ} :
  (x ≥ -3 / 2) ↔ (3 + 2 * x ≥ 0) := by
  constructor
  · -- Assume x ≥ -3/2, prove 3 + 2*x ≥ 0
    intro h
    linarith
  · -- Assume 3 + 2*x ≥ 0, prove x ≥ -3/2
    intro h
    linarith