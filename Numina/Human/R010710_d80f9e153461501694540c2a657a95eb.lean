import Mathlib

/- Completely factor the following expression: \[(15x^3+80x-5)-(-4x^3+4x-5).\] -/
theorem algebra_11417 (x : ℝ) : (15 * x ^ 3 + 80 * x - 5) - (-4 * x ^ 3 + 4 * x - 5) = 19 * x * (x ^ 2 + 4) := by
  ring