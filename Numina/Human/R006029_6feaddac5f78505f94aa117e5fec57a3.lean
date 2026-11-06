import Mathlib

/-Let $f(x)=\sin (\sin x)$. Evaluate $\lim _{h \rightarrow 0} \frac{f(x+h)-f(h)}{x}$ at $x=\pi$.-/
theorem calculus_611201 (f : ℝ → ℝ) (hf : f = Real.sin ∘ Real.sin) :
  Filter.Tendsto (λ h => (f (Real.pi + h) - f h) / Real.pi) (nhds 0) (nhds 0) := by
  -- The expression $\frac{f(x+h)-f(h)}{x}$ is continuous at $h=0$,
  have h1 : ContinuousAt (λ h => (f (Real.pi + h) - f h) / Real.pi) 0 := by
    have : ContinuousAt (λ h => (f (Real.pi + h) - f h)) 0 := by
      have : (fun x ↦ Real.sin (Real.pi + x)) = Real.sin ∘ (fun x ↦ Real.pi + x) := by
        ext x ;simp
      apply ContinuousAt.sub
      <;> apply continuous_iff_continuousAt.mp
      <;>  simp only [hf]
      apply Continuous.comp
      apply Real.continuous_sin
      rw [this]
      apply Continuous.comp Real.continuous_sin (continuous_add_left Real.pi)
      apply Continuous.comp
      <;> exact Real.continuous_sin
    exact ContinuousAt.div_const this Real.pi
  -- so the limit is just $\frac{f(x)-f(0)}{x}$.
  apply ContinuousAt.tendsto at h1
  -- Letting $x=\pi$ yields $\frac{\sin (\sin \pi)-\sin (\sin 0)}{\pi}=0$.
  have h2 : ((f (Real.pi + 0) - f 0) / Real.pi) = 0 := by
    rw [hf] ;norm_num
  rw [h2] at h1
  exact h1