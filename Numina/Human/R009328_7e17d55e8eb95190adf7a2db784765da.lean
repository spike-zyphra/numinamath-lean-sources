import Mathlib

/- Completely factor the following expression: \[(6a^3+92a^2-7)-(-7a^3+a^2-7)\] -/
theorem algebra_15367 (a : ℝ) : (6 * a ^ 3 + 92 * a ^ 2 - 7) - (-7 * a ^ 3 + a ^ 2 - 7) = 13 * a ^ 2 * (a + 7) := by
  ring_nf