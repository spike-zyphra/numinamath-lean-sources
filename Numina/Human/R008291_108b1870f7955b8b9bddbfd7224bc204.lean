import Mathlib

/- Factor $36-9x^2$. -/
theorem algebra_12638 (x : ℝ) : 36 - 9 * x ^ 2 = 9 * (2 - x) * (2 + x) := by
  ring_nf