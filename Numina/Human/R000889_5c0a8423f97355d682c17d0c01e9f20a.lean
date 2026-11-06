import Mathlib
/-Suppose that $f$ is an invertible function from $(-\infty,\infty)$ to $(-\infty,\infty)$.  If $f(f(x))=x$, find $f(x)-f^{-1}(x)$.-/
theorem algebra_18909 {f g : ℝ → ℝ} (hf : Function.LeftInverse f g) (hg : Function.RightInverse f g)
    (hfg : ∀ x, f (f x) = x) (hg2 : g = (Function.invFun f)): ∀ x, f x - g x = 0 := by
    --Applying $f^{-1}$ to both sides of the equation $f(f(x)) = x$, we get $f^{-1}(f(f(x))) = f^{-1}(x)$.  By definition of the inverse function, $f^{-1}(f(x)) = x$, so $f^{-1}(f(f(x))) = f(x)$.  Then $f(x) = f^{-1}(x)$, so $f(x) - f^{-1}(x) = \boxed{0}$.
    intro x
    have h :  g (x) = g (f (f x)) := by
      nth_rewrite 1[← hfg (x)]
      rfl
    have hf2 : Function.Involutive f := by
      rw[Function.Involutive]
      exact hfg
    have hf3 :  Function.Injective f := by
      apply Function.Involutive.injective hf2
    have h2 :  g ∘ f  =  id := by
      rw [hg2]
      apply Function.invFun_comp hf3
    rw[Function.comp_def] at h2
    have  h3 :  f (x) = g ( f ( f (x))) := by
      have e :  (fun x => g (f x)) (f (x))= f (x) := by
        rw[h2] ;rw [id]
      beta_reduce at e
      symm
      exact e
    rw [h3] ; rw [h] ; simp