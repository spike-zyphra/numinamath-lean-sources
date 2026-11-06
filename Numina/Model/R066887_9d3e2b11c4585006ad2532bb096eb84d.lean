import Mathlib

theorem algebra_4268 (x : ℝ) : 0 ≤ 21 - 7 * x ↔ x ≤ 3 := by
  constructor
  · -- Assume 0 ≤ 21 - 7x, prove x ≤ 3
    intro h
    linarith
  · -- Assume x ≤ 3, prove 0 ≤ 21 - 7x
    intro h
    linarith