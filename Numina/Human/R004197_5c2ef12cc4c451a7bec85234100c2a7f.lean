import Mathlib

/- Example 3 Let $y=f(x)$ be an increasing function on $\mathrm{R}$, and $f(x)=f^{-1}(x)$, then $f(x)=x$. -/
theorem algebra_241777 {f : ℝ → ℝ} (hf : Monotone f)
    (hinv : ∀ x, f (f x) = x) : ∀ x, f x = x := by
  -- We split on cases for f(x) < x, f(x) = x, and f(x) > x.
  intro x
  rcases lt_trichotomy (f x) x with (h | h | h)
  -- Suppose f x < x. Then x = f(f(x)) ≤ f(x) < x, a contradiction.
  . exfalso
    have : x < x := by
      refine lt_of_le_of_lt ?_ h
      nth_rw 1 [← hinv x]
      exact hf (le_of_lt h)
    exact lt_irrefl _ this
  -- If f(x) = x, we are done.
  . exact h
  -- The f(x) > x case is similar.
  . exfalso
    have : x < x := by
      refine lt_of_lt_of_le h ?_
      nth_rw 2 [← hinv x]
      exact hf (le_of_lt h)
    exact lt_irrefl _ this