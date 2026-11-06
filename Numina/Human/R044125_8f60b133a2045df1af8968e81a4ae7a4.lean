import Mathlib
set_option maxHeartbeats 0

open Filter Real

/-Compute $\lim _{x \rightarrow 0} \frac{e^{x \cos x}-1-x}{\sin \left(x^{2}\right)}$.-/
theorem calculus_611435 : Tendsto (fun x => (exp (x * cos x) - 1 - x) / sin (x ^ 2))
(nhdsWithin 0 {0}ᶜ) (nhds (1 / 2)) := by
-- Denote the function on the numerator by $f$
  let f := fun x => exp (x * cos x) - 1 - x
-- Denote the function on the denominator by $g$
  let g := fun x => sin (x ^ 2)
-- Compute the limit of $f$ at $0$
  have flim : Tendsto f (nhds 0) (nhds 0) := by
    nth_rw 2 [show 0 = f 0 by dsimp [f]; norm_num]; apply ContinuousAt.tendsto
    apply Continuous.continuousAt; dsimp [f]; continuity
-- Compute the limit of $g$ at $0$
  have glim : Tendsto g (nhds 0) (nhds 0) := by
    nth_rw 2 [show 0 = g 0 by dsimp [g]; norm_num]; apply ContinuousAt.tendsto
    apply Continuous.continuousAt; dsimp [f]; continuity
-- Compute the derivative of $f$
  have df : ∀ x, deriv f x = exp (x * cos x) * (cos x - x * sin x) - 1 := by
    intro x; dsimp [f]; rw [deriv_sub, deriv_id'', deriv_sub_const]
    simp; ring
    apply Differentiable.differentiableAt; apply Differentiable.sub_const
    apply Differentiable.exp; apply Differentiable.mul
    exact differentiable_id'; exact differentiable_cos
    exact differentiableAt_id'
-- Compute the derivative of $g$
  have dg : ∀ x, deriv g x = cos (x ^ 2) * (2 * x) := by intro; simp [g]
-- Compute the limit of $deriv f$ at $0$
  have dflim : Tendsto (deriv f) (nhds 0) (nhds 0) := by
    nth_rw 2 [show 0 = deriv f 0 by rw [df]; norm_num]; apply ContinuousAt.tendsto
    apply Continuous.continuousAt; rw [funext_iff.mpr df]; continuity
-- Compute the limit of $deriv g$ at $0$
  have dglim : Tendsto (deriv g) (nhds 0) (nhds 0) := by
    nth_rw 2 [show 0 = deriv g 0 by rw [dg]; norm_num]; apply ContinuousAt.tendsto
    apply Continuous.continuousAt; rw [funext_iff.mpr dg]; continuity
-- Compute the second derivative of $f$
  have d2f : ∀ x, deriv (deriv f) x = exp (x * cos x) * ((cos x - x * sin x) ^ 2 - 2 * sin x - x * cos x) := by
    intro x; rw [funext_iff.mpr df, deriv_sub_const, deriv_mul, _root_.deriv_exp]
    rw [deriv_mul, deriv_sub]; simp; ring
    any_goals exact differentiableAt_cos
    any_goals apply DifferentiableAt.mul
    any_goals exact differentiableAt_id'
    exact differentiableAt_sin; exact differentiableAt_cos
    apply DifferentiableAt.exp; apply DifferentiableAt.mul
    exact differentiableAt_id'; exact differentiableAt_cos
    apply DifferentiableAt.sub; exact differentiableAt_cos
    apply DifferentiableAt.mul; exact differentiableAt_id'
    exact differentiableAt_sin
-- Compute the second derivative of $g$
  have d2g : ∀ x, deriv (deriv g) x = -sin (x ^ 2) * (2 * x) ^ 2 + 2 * cos (x ^ 2) := by
    intro x; rw [funext_iff.mpr dg, deriv_mul, deriv_const_mul]; simp; ring
    exact differentiableAt_id'; apply DifferentiableAt.cos
    exact differentiableAt_pow 2; apply DifferentiableAt.const_mul
    exact differentiableAt_id'
-- Compute the limit of the second derivative of $f$ at $0$
  have d2flim : Tendsto (deriv (deriv f)) (nhds 0) (nhds 1) := by
    rw [show 1 = deriv (deriv f) 0 by rw [d2f]; norm_num]; apply ContinuousAt.tendsto
    apply Continuous.continuousAt; rw [funext_iff.mpr d2f]; continuity
-- Compute the limit of the second derivative of $g$ at $0$
  have d2glim : Tendsto (deriv (deriv g)) (nhds 0) (nhds 2) := by
    rw [show 2 = deriv (deriv g) 0 by rw [d2g]; norm_num]; apply ContinuousAt.tendsto
    apply Continuous.continuousAt; rw [funext_iff.mpr d2g]; continuity
-- Compute limit of the quotient of derivatives at $0$
  have d2divlim : Tendsto (fun x => deriv (deriv f) x / deriv (deriv g) x) (nhds 0) (nhds (1 / 2)) := by
    have := Tendsto.div d2flim d2glim (by simp)
    rw [show deriv (deriv f) / deriv (deriv g) = (fun x => deriv (deriv f) x / deriv (deriv g) x) by apply funext; intro; simp] at this
    exact this
-- Apply lhopital's rule to compute the limit of $deriv f / deriv g$ at $0$
  have ddivlim : Filter.Tendsto (fun x => deriv f x / deriv g x) (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2)) := by
    apply deriv.lhopital_zero_nhds
    · apply DifferentiableOn.eventually_differentiableAt
      apply Differentiable.differentiableOn; rw [funext_iff.mpr df]
      apply Differentiable.sub_const; apply Differentiable.mul
      apply Differentiable.exp; apply Differentiable.mul
      exact differentiable_id'; exact differentiable_cos
      apply Differentiable.sub; exact differentiable_cos
      apply Differentiable.mul; exact differentiable_id'
      exact differentiable_sin; exact (show Set.univ ∈ nhds 0 by simp)
    · apply d2glim.eventually_ne; simp
    exact dflim; exact dglim; exact d2divlim
-- Apply lhopital's rule again to compute the original limit
  rw [show (fun x => (rexp (x * cos x) - 1 - x) / sin (x ^ 2)) = (fun x => f x / g x) by apply funext; intro; dsimp [f, g]]
  apply deriv.lhopital_zero_nhds'
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    use 1; simp; intros; apply Differentiable.differentiableAt
    dsimp [f]; apply Differentiable.sub; apply Differentiable.sub_const
    apply Differentiable.exp; apply Differentiable.mul
    exact differentiable_id'; exact differentiable_cos
    exact differentiable_id'
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    use √(π / 2); constructor; positivity
    intro x hx xne; rw [dist_eq, lt_sqrt, sub_zero, sq_abs] at hx
    simp at xne; rw [dg]; intro h'; simp at h'; rcases h' with h'|_
    · suffices : 0 < cos (x ^ 2); linarith
      apply cos_pos_of_mem_Ioo; simp; constructor
      · have := pow_two_nonneg x; linarith
      exact hx
    contradiction; positivity
  · exact tendsto_nhdsWithin_of_tendsto_nhds flim
  · exact tendsto_nhdsWithin_of_tendsto_nhds glim
  exact ddivlim