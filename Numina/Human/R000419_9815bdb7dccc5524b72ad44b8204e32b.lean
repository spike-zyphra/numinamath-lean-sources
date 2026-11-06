import Mathlib

/-Define the function $f(x) = 2x - 5$. For what value of $x$ is $f(x)$ equal to $f^{-1}(x)$?-/
theorem algebra_10458 {f : ℝ → ℝ} ( x : ℝ )(hf : f = fun x => 2 * x - 5) (hx2 : f x = (Function.invFun f) x) : x = 5 := by
    have hx3 :  f ((Function.invFun f) x) = 2 * ((Function.invFun f) x) - 5 := by
      rw [hf]
    have h : ∃ a, f a = x := by
      use (1 / 2 * x + 2.5)
      rw [hf]; ring_nf
    --Substituting $f^{-1}(x)$ into our expression for $f$ we get  \[f(f^{-1}(x))=2f^{-1}(x)-5.\]Since $f(f^{-1}(x))=x$ for all $x$ in the domain of $f^{-1}$, we have \[x=2f^{-1}(x)-5.\]or  \[f^{-1}(x)=\frac{x+5}2.\]We want to solve the equation $f(x) = f^{-1}(x)$, so \[2x-5=\frac{x+5}2.\]or \[4x-10=x+5.\]Solving for $x$, we find $x = \boxed{5}$.
    have e : f (Function.invFun f x) = x := by
      apply Function.invFun_eq h

    rw [e] at hx3;
    have e2 := congrArg ( fun (t) => (t) / 2 + 2.5) hx3; beta_reduce at e2; ring_nf at e2
    rw [← e2] at hx2 ; rw[hf] at hx2 ;simp at hx2 ; ring_nf at hx2
    have e3 := congrArg ( fun (t) => (t)  - (1 / 2 * x)) hx2; beta_reduce at e3; ring_nf at e3
    have e4 := congrArg ( fun (t) => ((t) + 5) * (2 / 3)) e3; beta_reduce at e4; ring_nf at e4
    rw [e4]
