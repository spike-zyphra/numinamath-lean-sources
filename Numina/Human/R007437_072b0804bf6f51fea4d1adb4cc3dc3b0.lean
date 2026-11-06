import Mathlib

/- If $a,b,c$ satisfy the system of equations  \begin{align*}b + c &= 12-3a \\
a+c &= -14 - 3b \\
a+b &= 7 - 3c,
\end{align*} what is $2a + 2b + 2c$? -/
theorem algebra_11817 {a b c : ℝ} (h₀ : b + c = 12 - 3 * a) (h₁ : a + c = -14 - 3 * b)
    (h₂ : a + b = 7 - 3 * c) : 2 * a + 2 * b + 2 * c = 2 := by
  linarith