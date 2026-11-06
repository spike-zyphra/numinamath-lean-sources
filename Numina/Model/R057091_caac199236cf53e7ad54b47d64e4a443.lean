import Mathlib

theorem algebra_2546 (x : ℚ) : (19 * x - 96 = 96 - 19 * x) ↔ (x = 96 / 19) := by
  constructor
  · -- Assume $19x - 96 = 96 - 19x$, prove $x = 96/19$.
    intro h
    linarith
  · -- Assume $x = 96/19$, prove $19x - 96 = 96 - 19x$.
    intro h
    rw [h]
    norm_num