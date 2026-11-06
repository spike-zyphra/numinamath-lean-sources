import Mathlib

/- Completely factor the expression: $$x^8-256$$ -/
theorem algebra_12126 (x : ℝ) : x^8 - 256 = (x^4 + 16) * (x^2 + 4) * (x + 2) * (x - 2) := by ring
