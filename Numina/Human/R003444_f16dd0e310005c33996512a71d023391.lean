import Mathlib

/- 6. Let $f(x)$ be a function defined on the set of real numbers $R$, and satisfies the following relations:

$$

\begin{array}{l}
f(10+x)=f(10-x) . \\
f(20-x)=-f(20+x) .
\end{array}

$$


Then $f(x)$ is
(A) an even function and a periodic function;
(B) an even function, but not a periodic function;
(C) an odd function and a periodic function;
(D) an odd function, but not a periodic function.
Answer ( $\quad$ ) -/
theorem algebra_182664 {f : ℝ → ℝ} (h1 : ∀ x, f (10 + x) = f (10 - x)) (h2 : ∀ x, f (20 - x) = -f (20 + x)) :
    (∃ c, Function.Periodic f c) ∧ Function.Odd f := by
  -- to show f is odd, use the first and second relations with well-chosen arguments
  have odd_f : Function.Odd f
  · intro x
    have h1' := h1 (-x - 10)
    have h1'' := h1 (10 - x)
    have h2' := h2 (-x)
    ring_nf at h1' h1'' h2'
    rw [h1', h2', h1'']
  constructor
  -- to show f is periodic, use the first and second relations and use that f odd
  · use 40
    intro x
    rw [add_comm]
    have h1' := h1 (10 - x)
    ring_nf at h1'
    have h2' := h2 (-x - 20)
    ring_nf at h2'
    rw [h2', odd_f x, neg_neg]
  exact odd_f