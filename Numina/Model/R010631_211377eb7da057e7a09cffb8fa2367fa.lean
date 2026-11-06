import Mathlib

theorem algebra_9073 (x : ℝ) : 3 * x - 4 > 2 ↔ x > 2 := by
  constructor
  · -- Proof of the forward direction: If 3x - 4 > 2, then x > 2.
    intro h
    linarith
  · -- Proof of the reverse direction: If x > 2, then 3x - 4 > 2.
    intro h
    linarith