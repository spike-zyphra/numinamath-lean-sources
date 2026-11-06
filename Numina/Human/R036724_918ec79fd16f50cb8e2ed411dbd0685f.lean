import Mathlib

/- All triangles have the same value, and all circles have the same value. What is the sum of two circles? \begin{align*}
\Delta + \bigcirc + \Delta + \bigcirc + \Delta + \bigcirc + \Delta + \Delta&= 21\\
\bigcirc + \Delta+\bigcirc+\Delta+\bigcirc + \Delta + \bigcirc + \bigcirc &= 16\\
\bigcirc + \bigcirc &= \ \, ?
\end{align*} -/
theorem algebra_21881 {a b : ℝ}
    (h1 : a + b + a + b + a + b = 21) (h2 : b + a + b + a + b + a = 16) :
    b + b = 17 / 8 := by
        linarith