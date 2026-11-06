import Mathlib

/- Solve for $x$: $3x-(1-x)=5$. Express your answer as a common fraction in simplest form. -/
theorem algebra_20485 (x : ℚ) (h : 3 * x - (1 - x) = 5) : x = 3 / 2:= by
  linarith
