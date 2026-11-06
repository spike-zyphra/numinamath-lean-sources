import Mathlib
/- Let $x, y, z$ be real numbers satisfying

$$
\begin{aligned}
2 x+y+4 x y+6 x z & =-6 \\
y+2 z+2 x y+6 y z & =4 \\
x-z+2 x z-4 y z & =-3
\end{aligned}
$$

Find $x^{2}+y^{2}+z^{2}$. -/
theorem algebra_610370 (x y z : ℝ) (h1 : 2 * x + y + 4 * x * y + 6 * x * z = -6) (h2 : y + 2 * z + 2 * x * y + 6 * y * z = 4) (h3 : x - z + 2 * x * z - 4 * y * z = -3) : x ^ 2 + y ^ 2 + z ^ 2 = 29:= by
  have h4 : z = 5 - x - y:= by linarith
  subst z
  clear h3
  linarith
