import Mathlib

/- Given that the function $f(x)$ is an odd function, and when $x \leq 0$, $f(x) = x^2 - 2x$, find the expression for $f(x)$ when $x > 0$.-/
theorem algebra_9169 {f : ℝ → ℝ} (hfodd : ∀ x, f (- x) = -f x) (hf : ∀ x ≤ 0, f x = x ^ 2 - 2 * x) :
    ∀ x > 0, f x = -x ^ 2 - 2 * x := by
  -- From the given information, let's assume $x > 0$, then $-x < 0$;
  -- Since when $x \leq 0$, $f(x) = x^2 - 2x$,
  -- Therefore, $f(-x) = (-x)^2 + 2(-x) = x^2 + 2x$,
  -- Because the function $f(x)$ is an odd function,
  -- It follows that $f(-x) = -f(x)$,
  -- Thus, when $x > 0$, $f(x) = -x^2 - 2x$,
  -- Hence, the answer is $f(x) = -x^2 - 2x$.
  -- $\boxed{\text{The expression for } f(x) \text{ when } x > 0 \text{ is } -x^2 - 2x.}$
  intro x hx
  specialize hf (-x) (by linarith)
  rw [hfodd] at hf
  linear_combination -hf
