import Mathlib
/-Suppose that $\Join$ is an operation defined by $x \Join y = (x+2)(y-3)$. What is $((t) \Join (t+2)) - ((t+1) \Join (t+1))$?-/
theorem algebra_19950 {t : ℤ} (h : f = fun x y => (x + 2) * (y - 3)) : f t (t + 2) - f (t + 1) (t + 1) = 4 := by
  --First, we evaluate the first pair of parentheses:
  --\begin{align*}
  --(t) \Join (t+2) &= (t + 2)((t+2) - 3) \\
  --&= (t+2)(t - 1)\\
  --&= t^2 + 2t - t - 2\\
  --&= t^2 + t - 2.
  --\end{align*}
  rw [h]; beta_reduce --Substitute into the expression
  --Next, we evaluate the second pair of parentheses:
  --\begin{align*}
  --(t + 1) \Join (t+1) &= ((t+1) + 2)((t+1) - 3) \\
  --&= (t+3)(t - 2) \\
  --&= t^2 + 3t - 2t - 6 \\
  --&= t^2 + t - 6.
  --\end{align*}Subtracting the two expressions and noting that certain terms cancel, we obtain $(t^2 + t - 2) - (t^2 + t - 6) = -2 - (-6) = \boxed{4}$.
  ring_nf --Confirmation of calculation results