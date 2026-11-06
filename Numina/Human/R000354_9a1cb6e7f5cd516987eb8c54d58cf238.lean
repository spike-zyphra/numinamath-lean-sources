import Mathlib

/- Given that the function $f(x)$ is an even function defined on $(-\infty, +\infty)$. When $x \in (-\infty, 0)$, $f(x) = x - x^4$. Find the expression for $f(x)$ when $x \in (0, +\infty)$.-/
theorem algebra_9093 {f : ℝ → ℝ} (h₀ : ∀ x, f (-x) = f x)
    (h₁ : ∀ x < 0, f x = x - x ^ 4) :
    ∀ x > 0, f x = -x ^ 4 - x := by
  intro x hx
  -- Let $x \in (0, +\infty)$, then $-x \in (-\infty, 0)$.
  -- Since when $x \in (-\infty, 0)$, $f(x) = x - x^4$, we have $f(-x) = -x - (-x)^4$.
  specialize h₁ (-x) (by linarith)
  -- Given that $f(x)$ is an even function defined on $(-\infty, +\infty)$,
  --we have $f(x) = f(-x) = -x - x^4$.
  rw [h₀] at h₁
  -- Therefore, the answer is $\boxed{-x^4 - x}$.
  linear_combination h₁
