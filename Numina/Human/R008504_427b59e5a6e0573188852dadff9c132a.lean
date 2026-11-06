import Mathlib

/- Write the expression $\frac{4+3c}{7}+2$ as a single fraction. -/
theorem algebra_15620 (c : ℝ) : (4 + 3 * c) / 7 + 2 = (18 + 3 * c) / 7 := by
  ring_nf