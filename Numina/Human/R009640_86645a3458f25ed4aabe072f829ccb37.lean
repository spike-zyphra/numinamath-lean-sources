import Mathlib

/- Find $x$ so that the arithmetic mean of $x, 3x, 1000$, and $3000$ is $2018$. -/
theorem algebra_54606 (x : ℝ) (h : (x + 3 * x + 1000 + 3000) / 4 = 2018) : x = 1018 := by 
  nlinarith