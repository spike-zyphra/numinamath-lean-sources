import Mathlib

open Real Set

/-Suppose $f$ is a differentiable real function
such that $f(x)+f^{\prime}(x) \leq 1$ for all $x$, and $f(0)=0$.
What is the largest possible value of $f(1)$ ?
(Hint: consider the function $e^{x} f(x)$.)-/
theorem calculus_610988 :
    IsGreatest { a : ℝ | ∃ f : ℝ → ℝ, Differentiable ℝ f ∧ (∀ x, f x + deriv f x ≤ 1) ∧ f 0 = 0 ∧ a = f 1 }
    ((exp 1 - 1) / exp 1) := by
  constructor
  · simp only [mem_setOf_eq]
    let f : ℝ → ℝ := fun x ↦ 1 - exp (- x) --
    -- This maximum is attained if we actually have $g^{\prime}(x)=e^{x}$ everywhere
    use f
    have hf : Differentiable ℝ f := by
      apply Differentiable.sub
      · exact differentiable_const 1 
      · apply Differentiable.exp 
        exact differentiable_neg
    have df : deriv f = fun x ↦ exp (- x) := by
      ext x 
      rw [deriv_sub, _root_.deriv_exp] 
      simp only [deriv_const', deriv_neg'', mul_neg, mul_one, sub_neg_eq_add, zero_add]
      · exact differentiable_neg x 
      · exact (differentiable_const 1 x)
      · apply Differentiable.exp 
        exact differentiable_neg
    refine ⟨hf, ?_, ?_, ?_⟩ 
    · intro x 
      rw [df] 
      simp [f]
    -- this entails the requirement $f(x)+f^{\prime}(x)=1$, which is met by $f(x)=1-e^{-x}$.
    · simp [f]
    · unfold f 
      rw [exp_neg]
      field_simp 
  · intro _ ha
    obtain ⟨f, df, hf, h0, rfl⟩ := ha
    let g : ℝ → ℝ := fun x => exp x * f x -- Let $g(x)=e^{x} f(x)$
    let g' : ℝ → ℝ := fun x => exp x * (f x + deriv f x)
    have hg : Differentiable ℝ g := Differentiable.mul differentiable_exp df
    have dg : deriv g = g' := by
      ext x
      rw [deriv_mul (differentiable_exp x) (df x)]
      simp only [Real.deriv_exp, Pi.mul_apply, Pi.add_apply]
      ring
    have hcont : ContinuousOn g (Icc 0 1) := by
      apply Continuous.continuousOn
      exact Differentiable.continuous hg
    have hderiv : ∀ x ∈ Ioo 0 1, HasDerivWithinAt g (g' x) (Ioi x) x := by
      rw [← dg]
      intro x _
      apply HasDerivAt.hasDerivWithinAt
      rw [hasDerivAt_deriv_iff]
      exact hg x
    have φint : MeasureTheory.IntegrableOn exp (Icc 0 1) MeasureTheory.volume := by
      apply ContinuousOn.integrableOn_Icc
      apply Continuous.continuousOn
      exact continuous_exp
    have hφg : ∀ x ∈ Ioo 0 1, g' x ≤ exp x := by
    -- then $g^{\prime}(x)=e^{x}\left(f(x)+f^{\prime}(x)\right) \leq e^{x}$
      intro x hx
      calc
        _ ≤ (exp x) * (1 : ℝ) := by
          apply mul_le_mul_of_nonneg_left
          · exact hf x
          · exact exp_nonneg x
        _ ≤ exp x := by rw [mul_one]
    have le := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
      (by norm_num) hcont hderiv φint hφg
    simp only [exp_zero, h0, mul_zero, sub_zero, integral_exp, g] at le 
    -- Integrating from 0 to 1 , we have $g(1)-g(0)=\int_{0}^{1} g^{\prime}(x) d x \leq \int_{0}^{1} e^{x} d x=e-1$. 
    rw [le_div_iff₀ (exp_pos 1), mul_comm]
    -- But $g(1)-g(0)=e \cdot f(1)$, so we get $f(1) \leq(e-1) / e$. 
    exact le
