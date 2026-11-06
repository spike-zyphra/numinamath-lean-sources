import Mathlib

/- Given $f(x) = \begin{cases} x^{2}-2x, & x\geq 0 \\ g(x), & x<0\end{cases}$ is an odd function, then $g(x) = \_\_\_\_\_\_$. -/
theorem algebra_9336 {f g : ℝ → ℝ} (hf : ∀ x, x ≥ 0 → f x = x ^ 2 - 2 * x)(hg : ∀ x, x < 0 → f x = g x) (hodd : Function.Odd f) : ∀x, x < 0 → g x = -x ^ 2 - 2 * x := by
intro x negx
have: (-x) ≥ 0 := by linarith [negx]
have feq: f (-x) = - f x := hodd x
rw [hf, hg] at feq
linarith [feq]
simp [negx, this]
simp [this]
