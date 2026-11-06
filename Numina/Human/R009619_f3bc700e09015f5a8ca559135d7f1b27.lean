import Mathlib

/- The general form of the quadratic equation $4x = x^{2} - 8$ is _______. -/
theorem algebra_9455 (x : ℝ) : 4 * x = x ^ 2 - 8 ↔ x ^ 2 - 4 * x - 8 = 0 := by
  -- Split the goal into two implications
  -- And linarith can solve both
  constructor <;> intro h <;> linarith
