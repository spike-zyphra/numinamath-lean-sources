import Mathlib

/- Let  \[ f(x) =
\begin{cases}
-x^2 & \text{if } x \geq 0,\\
x+8& \text{if } x <0.
\end{cases}
\]Compute $f(f(f(f(f(1))))).$ -/
theorem algebra_10318 {f : ℝ → ℝ} (hf : ∀ x, x ≥ 0 → f x = -x ^ 2)
    (hf' : ∀ x, x < 0 → f x = x + 8) :
    f (f (f (f (f 1)))) = -33 := by 
  norm_num [hf, hf']