import Mathlib

/- Suppose that $x,$ $y,$ and $z$ satisfy the equations
\begin{align*}
xyz &= 4, \\
x^3 + y^3 + z^3 &= 4, \\
xy^2 + x^2 y + xz^2 + x^2 z + yz^2 + y^2 z &= 12.
\end{align*}Calculate the value of $xy + yz + zx.$ -/
theorem algebra_20773 {x y z : ℝ} (h₀ : x * y * z = 4) (h₁ : x ^ 3 + y ^ 3 + z ^ 3 = 4)
    (h₂ : x * y ^ 2 + x ^ 2 * y + x * z ^ 2 + x ^ 2 * z + y * z ^ 2 + y ^ 2 * z = 12) :
    x * y + y * z + z * x = 6 := by 
  nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
    sq_nonneg (x + y + z - 3)]