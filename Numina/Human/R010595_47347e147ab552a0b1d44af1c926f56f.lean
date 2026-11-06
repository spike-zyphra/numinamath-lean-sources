import Mathlib

/- Given that the function $f(x)$ is defined on $\mathbb{R}$, then the function $g(x) = f(x) + f(-x)$ is (fill in "odd function", "even function", or "neither odd nor even").-/
theorem algebra_9248 {f : ℝ → ℝ} (g : ℝ → ℝ) (h₀ : ∀ x, g x = f x + f (-x)) :
    ∀ x, g (-x) = g x := by
--   Since the domain of the function is $\mathbb{R}$,
-- $\because g(-x) = f(-x) + f(x) = g(x)$
-- $\therefore$ the function $g(x) = f(x) + f(-x)$ is an even function.
-- Hence, the answer is: $\boxed{\text{even function}}$
  intro x
  rw [h₀, h₀, neg_neg, add_comm]
