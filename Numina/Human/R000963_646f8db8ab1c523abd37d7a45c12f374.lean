import Mathlib

/- If $x$ is a real number, find $49x^2+14x(19-7x)+(19-7x)^2$. -/
theorem algebra_19418 (x : ℝ) : 49 * x ^ 2 + 14 * x * (19 - 7 * x) + (19 - 7 * x) ^ 2 = 361 := by 
  ring_nf