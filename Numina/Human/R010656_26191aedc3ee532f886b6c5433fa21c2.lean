import Mathlib

/- If $x$, $y$, and $z$ are positive real numbers satisfying: \begin{align*}
\log x - \log y &= a, \\
\log y - \log z &= 15, \text{ and} \\
\log z - \log x &= -7, \\
\end{align*}where $a$ is a real number, what is $a$? -/
theorem algebra_22192 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : Real.log x - Real.log y = a) (h2 : Real.log y - Real.log z = 15) (h3 : Real.log z - Real.log x = -7) :
    a = -8 := by
  linarith