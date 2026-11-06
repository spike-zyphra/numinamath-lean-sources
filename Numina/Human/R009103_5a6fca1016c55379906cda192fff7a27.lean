import Mathlib

/- If the system of equations

\begin{align*}
6x-4y&=a,\\
6y-9x &=b.
\end{align*}has a solution $(x, y)$ where $x$ and $y$ are both nonzero, find $\frac{a}{b},$ assuming $b$ is nonzero. -/
theorem algebra_14297 {x y a b : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h1 : 6 * x - 4 * y = a) (h2 : 6 * y - 9 * x = b)
    (hb : b ≠ 0) : a / b = -2 / 3 := by 
  field_simp
  ring_nf
  linarith