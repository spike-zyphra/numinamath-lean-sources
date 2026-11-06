import Mathlib

/- Solve the following system of equations for $c$:
\begin{align*}
a - b &= 2 (c+d)\\
b &= a-2 \\
d &= c+5
\end{align*} -/
theorem algebra_21858 {a b c d : ℝ} (h₀ : a - b = 2 * (c + d)) (h₁ : b = a - 2) (h₂ : d = c + 5) :
    c = -2 := by
    linarith    -- solve the system of equations
