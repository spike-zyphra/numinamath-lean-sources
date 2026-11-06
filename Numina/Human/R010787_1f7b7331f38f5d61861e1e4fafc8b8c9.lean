import Mathlib

/- Simplify $\frac{x+1}{3}+\frac{2-3x}{2}$.  Express your answer as a single fraction. -/
theorem algebra_11825 (x : ℝ) : (x + 1) / 3 + (2 - 3 * x) / 2 = (8 - 7 * x) / 6 := by
  ring_nf