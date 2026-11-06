import Mathlib

/- The value of $2x+10$ is half of the value of $5x+30$. What is the value of $x$? -/
theorem algebra_15830 (x : ℝ) (h : 2 * x + 10 = (5 * x + 30) / 2) : x = -10 := by
  linarith