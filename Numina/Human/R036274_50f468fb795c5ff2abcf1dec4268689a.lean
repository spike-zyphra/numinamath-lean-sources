import Mathlib

/- Given that $f(x)$ is a periodic function on $\mathbb{R}$ with the smallest positive period of $2$, and when $0 \leqslant x < 2$, $f(x)=x^3-x$, find the expression for $f(x)$ when $x \in [-2,0)$. -/
theorem algebra_9459 {f : ℝ → ℝ} (hf : Function.Periodic f 2)
    (h : ∀ x ∈ Set.Ico 0 2, f x = x ^ 3 - x) :
    ∀ x ∈ Set.Ico (-2) 0, f x = x ^ 3 + 6 * x ^ 2 + 11 * x + 6 := by
  intro x hx
  simp at h hx
  -- f(x) = f(x+2) = (x+2)^3 - (x+2) = x^3 + 6x^2 + 11x + 6
  calc f x = f (x + 2) := symm (hf x)
       _ = (x + 2) ^ 3 - (x + 2) := h _ (by linarith) (by linarith)
       _ = x ^ 3 + 6 * x ^ 2 + 11 * x + 6 := by ring
