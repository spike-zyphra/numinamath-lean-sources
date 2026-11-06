import Mathlib

/-Let $f(x)$ be a polynomial such that
\[f(x^2 + 1) = x^4 + 4x^2.\]Find $f(x^2 - 1).$-/
theorem algebra_14948 {f : Polynomial ℝ} (h : ∀ x, f.eval (x ^ 2 + 1) = x ^ 4 + 4 * x ^ 2) :
∀ x, f.eval (x ^ 2 - 1) = x ^ 4 - 4 := by
-- Prove that $f$ is equal to $x^2+2*x-3$ by apply Polynomial.eq_of_infinite_eval_eq and Set.infinite_of_forall_exists_gt
  have aux : f = (Polynomial.X) ^ 2 + 2 * Polynomial.X - Polynomial.C 3 := by
    apply Polynomial.eq_of_infinite_eval_eq
    have : Set.Ici 1 ⊆ {x |Polynomial.eval x f =
    Polynomial.eval x ((Polynomial.X) ^ 2 + 2 * Polynomial.X - Polynomial.C 3)} := by
      intro x; simp; intro hx
      have := h (Real.sqrt (x-1))
      have aux' : (Real.sqrt (x-1)) ^ 2 = x - 1 := by
        rw [pow_two, ← Real.sqrt_mul, Real.sqrt_mul_self]; any_goals linarith
      rw [show 4=2*2 by norm_num, pow_mul, aux'] at this
      norm_num at this; rw [this]; ring
    rw [Set.subset_def] at this; simp at this
    apply Set.infinite_of_forall_exists_gt; simp
    intro a; use max (a+1) 1; simp; apply this; simp
-- Plug in $x^2-1$ to the explicit expression of $f$ in aux and simplify
  intro x; rw [aux]; simp; ring