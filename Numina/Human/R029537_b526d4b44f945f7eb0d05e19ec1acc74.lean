import Mathlib

/- If

\begin{align*}
3x+4y-12z&=10,\\
-2x-3y+9z&=-4,
\end{align*}

compute $x$. -/
theorem algebra_21456 {x y z : ℝ} (h1 : 3 * x + 4 * y - 12 * z = 10) (h2 : -2 * x - 3 * y + 9 * z = -4) :
    x = 14 := by 
  have h3 := h1
  linarith