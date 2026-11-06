import Mathlib

/- If $w$, $x$, $y$, and $z$ are real numbers satisfying: \begin{align*}
w+x+y &= -2, \\
w+x+z &= 4, \\
w+y+z &= 19, \text{ and} \\
x+y+z &= 12,
\end{align*} what is $wx + yz$? -/
theorem algebra_16312 {w x y z : ℝ} (h₀ : w + x + y = -2) (h₁ : w + x + z = 4)
    (h₂ : w + y + z = 19) (h₃ : x + y + z = 12) : w * x + y * z = 99 := by
  have h₄ : w = -2 - x - y := by linarith
  rw [h₄] at *
  nlinarith