import Mathlib

/- The average of $x+6$, $6x+2$, and $2x+7$ is $4x-7$. What is $x$? -/
theorem algebra_13577 (x : ℝ) (h : (x + 6 + 6 * x + 2 + 2 * x + 7) / 3 = 4 * x - 7) :
    x = 12 := by
  nlinarith