import Mathlib

/-- Here are two functions: $$\begin{array}{ccc}
f(x) & = & 3x^2-2x+ 4\\
g(x) & = & x^2-kx-6
\end{array}$$ If $f(10) - g(10) = 10,$ what is the value of $k?$-/
theorem algebra_4111 {k : ℝ} {f g : ℝ → ℝ}
    (hf : ∀ x, f x = 3 * x ^ 2 - 2 * x + 4) (hg : ∀ x, g x = x ^ 2 - k * x - 6)
    (eq : f 10 - g 10 = 10) : k = -18 := by
  rw [hf, hg, ← sub_eq_zero] at eq
  -- Automatically solve linear equations about `k` using the `linarith` 
  linarith
