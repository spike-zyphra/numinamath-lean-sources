import Mathlib
/- Suppose that $x, y, z$ are real numbers such that

$$
x=y+z+2, \quad y=z+x+1, \quad \text { and } \quad z=x+y+4
$$

Compute $x+y+z$. -/
theorem algebra_609303 (x y z : ℝ) (h1 : x = y + z + 2) (h2 : y = z + x + 1) (h3 : z = x + y + 4) : x + y + z = -7:= by
  -- use linarith to solve the problem
  linarith
