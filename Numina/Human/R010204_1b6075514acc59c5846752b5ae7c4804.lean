import Mathlib

/- For any real numbers $a$ and $b$, the identity $a^{2} + b^{2} + 2ab = (a + b)^{2}$ holds true. -/
theorem algebra_9208 {a b : ℝ} : a^2 + b^2 + 2 * a * b = (a + b)^2 := by
  ring
