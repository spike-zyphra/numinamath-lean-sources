import Mathlib
/- Solve for $x$ in the equation $20 \cdot 14+x=20+14 \cdot x$. -/
theorem algebra_609299 (x : ℝ) (h : 20 * 14 + x = 20 + 14 * x) : x = 20:= by
  -- use linarith to solve the equation
  linarith
