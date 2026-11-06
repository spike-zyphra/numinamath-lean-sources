import Mathlib

/--
For real numbers $a$ and $b$, define $a\textdollar b = (a - b)^2$. What is $(x - y)^2\textdollar(y - x)^2$?
$\textbf{(A)}\ 0 \qquad \textbf{(B)}\ x^2 + y^2 \qquad \textbf{(C)}\ 2x^2 \qquad \textbf{(D)}\ 2y^2 \qquad
\textbf{(E)}\ 4xy$
-/
theorem algebra_1199 (x y : ℝ) : ((x - y)^2 - (y - x)^2)^2 = 0 := by
  -- Because $(-z)^2 = z^2$, the expression simplifies to $(x - y)^2 - (y - x)^2 = 0$.
  calc _ = ((x - y)^2 - ((-1) * (x - y))^2)^2 := by simp
       _ = ((x - y)^2 - (x - y)^2)^2 := by rw [mul_pow]; simp
        _ = 0^2 := by simp
        _ = 0 := by simp