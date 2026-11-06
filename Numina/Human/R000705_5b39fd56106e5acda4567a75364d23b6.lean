import Mathlib

/- Given that

\begin{align*}
\frac{1}{x}+\frac{1}{y}&=3,\\
xy+x+y&=4,
\end{align*}

compute $x^2y+xy^2$. -/
theorem algebra_14128 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h1 : 1 / x + 1 / y = 3) (h2 : x * y + x + y = 4) :
    x ^ 2 * y + x * y ^ 2 = 3 := by
  field_simp [hx, hy] at h1
  nlinarith
  <;> nlinarith