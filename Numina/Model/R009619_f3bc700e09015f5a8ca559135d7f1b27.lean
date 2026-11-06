import Mathlib

theorem algebra_9455 (x : ℝ) : 4 * x = x ^ 2 - 8 ↔ x ^ 2 - 4 * x - 8 = 0 := by
  constructor
  · -- Assume $4x = x^2 - 8$ and prove $x^2 - 4x - 8 = 0$
    intro h
    linarith
  · -- Assume $x^2 - 4x - 8 = 0$ and prove $4x = x^2 - 8$
    intro h
    linarith