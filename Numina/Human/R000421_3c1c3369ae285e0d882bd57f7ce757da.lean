import Mathlib
/-Let $t(x) = 3x-8$ and $s(t(x)) = x^2 + 3x - 2$.  Find $s(1)$.-/
theorem algebra_10480 {s t : ℝ → ℝ} (ht : t = fun x => 3 * x - 8) (hs : s ∘ t = fun x => x ^ 2 + 3 * x - 2) :
    s 1 = 16 := by
  rw [Function.comp_def] at hs
  rw [ht] at hs; simp at hs
  --We don't know $s(x)$, so we don't have an expression we can simply stick $1$ in to get an answer. We do, however, know that $s(t(x)) = x^2 +3x-2$.  So, if we can figure out what to put into $t(x)$ such that $1$ is output, we can use our expression for $s(t(x))$ to find $s(1)$.
  --If $t(x) = 1$, then $3x-8=1$, which gives $x =3$, so $t(3)=1$.  Therefore, we have $s(t(3)) = s(1)$.  But we also know that $s(t(x)) = x^2 + 3x-2$, so $s(t(3)) = 3^2 +3(3) -2 = \boxed{16}$.
  have e := congrArg ( fun (n) => (n) 3 ) hs; simp at e; ring_nf at e
  exact e