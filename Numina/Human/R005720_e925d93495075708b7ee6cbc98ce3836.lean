import Mathlib
/- If $x+2 y-3 z=7$ and $2 x-y+2 z=6$, determine $8 x+y$. -/
theorem algebra_609588 (x y z : ℝ) (h1 : x + 2 * y - 3 * z = 7) (h2 : 2 * x - y + 2 * z = 6) : 8 * x + y = 32:= by
  -- use linarith to solve the system of equations
  linarith
