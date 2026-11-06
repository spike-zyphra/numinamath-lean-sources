import Mathlib

/- Given that

\begin{align*}
\frac{1}{x}+\frac{1}{y}&=5,\\
3xy+x+y&=4,
\end{align*}

compute $x^2y+xy^2$. -/
theorem algebra_19566 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : 1 / x + 1 / y = 5) (h2 : 3 * x * y + x + y = 4) :
    x ^ 2 * y + x * y ^ 2 = 5 / 4 := by
  -- Cancel the denominators at h1
  field_simp at h1
  -- Solve the system of equations about x*y and x+y
  replace ⟨h1, h2⟩ : x * y = 1/2 ∧ x + y = 5/2 := by constructor <;> linarith
  -- Compute x^2y+xy^2 = xy(x+y)
  calc x ^ 2 * y + x * y ^ 2
       _ = x * y * (x + y) := by ring
       _ = (1/2) * (5/2) := by rw [h1, h2]
       _ = 5 / 4 := by norm_num
