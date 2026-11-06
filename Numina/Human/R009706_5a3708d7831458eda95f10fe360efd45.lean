import Mathlib

/- Completely factor the following expression: \[(9x^5+25x^3-4)-(x^5-3x^3-4).\] -/
theorem algebra_13114 (x : ℝ) : (9 * x ^ 5 + 25 * x ^ 3 - 4) - (x ^ 5 - 3 * x ^ 3 - 4) =
    4 * x ^ 3 * (2 * x ^ 2 + 7) := by
  ring_nf