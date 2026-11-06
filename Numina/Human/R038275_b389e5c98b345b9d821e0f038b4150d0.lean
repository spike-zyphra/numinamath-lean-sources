import Mathlib

/- If \begin{align*}
4x-y+2z&=7,\\
6x+3y+3z&=5,
\end{align*} compute $y$. -/
theorem algebra_22200 (x y z : ℝ) (h1 : 4 * x - y + 2 * z = 7) (h2 : 6 * x + 3 * y + 3 * z = 5) :
    y = -11 / 9 := by 
  ring_nf at *
  linarith