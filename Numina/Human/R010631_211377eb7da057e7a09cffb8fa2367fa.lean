import Mathlib

/- The solution set of the inequality $3x-4 \gt 2$ is ______.-/
theorem algebra_9073 (x : ℝ) : 3 * x - 4 > 2 ↔ x > 2 := by
  -- To solve the inequality $3x - 4 > 2$, we follow these steps:
  -- 1. Start with the given inequality:
  -- \[3x - 4 > 2\]
  -- 2. Add $4$ to both sides to isolate the term with $x$:
  -- \[3x - 4 + 4 > 2 + 4\]
  -- \[3x > 6\]
  -- 3. Divide both sides by $3$ to solve for $x$:
  -- \[\frac{3x}{3} > \frac{6}{3}\]
  -- \[x > 2\]
  -- Therefore, the solution set of the inequality is $\boxed{x > 2}$.
  constructor <;> intro h <;> linarith
