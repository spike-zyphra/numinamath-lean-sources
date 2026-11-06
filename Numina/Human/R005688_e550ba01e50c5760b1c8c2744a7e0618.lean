import Mathlib
open Complex
/- The complex numbers $x, y, z$ satisfy

$$
\begin{aligned}
x y z & =-4 \\
(x+1)(y+1)(z+1) & =7 \\
(x+2)(y+2)(z+2) & =-3
\end{aligned}
$$

Find, with proof, the value of $(x+3)(y+3)(z+3)$. -/
theorem algebra_609417 (x y z : ℂ) (h1 : x * y * z = -4) (h2 : (x + 1) * (y + 1) * (z + 1) = 7) (h3 : (x + 2) * (y + 2) * (z + 2) = -3) : (x + 3) * (y + 3) * (z + 3) = -28:= by
  -- use linear combination to solve the problem
  linear_combination h1 - 3 * h2 + 3 * h3
