import Mathlib

open Topology Filter Real

/- ## Problem Statement

Calculate the limit of the function:

$\lim _{x \rightarrow a}\left(\frac{\sin x}{\sin a}\right)^{\frac{1}{x-a}}$ -/
theorem calculus_122196 (a : ℝ) (ha : sin a ≠ 0) :
    Tendsto (λ x => (sin x / sin a) ^ (1 / (x - a)) ) (𝓝[≠] a) (𝓝 (Real.exp (Real.cot a))) := by
  -- Show that there exists s ∈ 𝓝[≠] a such that 0 < sin x / sin a for all x ∈ s.
  have ⟨s, hs, hs1⟩ : ∃ s, s ∈ 𝓝[≠] a ∧ ∀ x ∈ s, 0 < sin x / sin a := by
    -- sin x / sin a is continuous at a and 0 < 1 = sin a / sin a,
    -- so there exists e > 0 such that 0 < sin x / sin a for all x ∈ Metric.ball a e.
    have := ContinuousAt.eventually_lt (f := fun x : ℝ => 0) (g := fun x => sin x / sin a) (x₀ := a) (by fun_prop) (by fun_prop) (by simp [div_self ha])
    simp only [Metric.eventually_nhds_iff_ball] at this
    have ⟨e, he, h⟩ := this
    -- Take s = {a}ᶜ ∩ Metric.ball a e.
    use {a}ᶜ ∩ Metric.ball a e
    constructor
    · -- Show that {a}ᶜ ∩ Metric.ball a e ∈ 𝓝[≠] a.
      apply inter_mem_nhdsWithin
      exact Metric.ball_mem_nhds a he
    · -- Show that 0 < sin x / sin a for all x ∈ s.
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff, and_imp]
      intro x hxa
      apply h
  -- Show that (sin x / sin a) ^ (1 / (x - a)) = exp (log (sin x / sin a) / (x - a))
  -- for all x ∈ s.
  apply Tendsto.congr' (f₁ := exp ∘ fun x => log (sin x / sin a) / (x - a))
  · simp_rw [EventuallyEq, eventually_iff_exists_mem]
    use s, hs
    intro x hx
    simp [rpow_def_of_pos (hs1 x hx)]
    ring_nf
  -- exp(x) is continuous, so it is enough to show that the limit of
  -- log (sin x / sin a) / (x - a) is cot(a) as x tends to a.
  apply Tendsto.comp (Continuous.tendsto continuous_exp _)
    -- Apply L'Hôpital's rule.
  apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => (cos x / sin a) / (sin x / sin a)) (g' := fun x => 1)
  · -- Show that the derivative of log (sin x / sin a) is
    -- (cos x / sin a) / (sin x / sin a) for x ∈ s.
    rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    apply HasDerivAt.log _ (by linarith [hs1 x hx])
    apply HasDerivAt.div_const
    exact hasDerivAt_sin x
  · -- Show that the derivative of x - a is 1 for x ∈ s.
    rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    apply HasDerivAt.sub_const
    exact hasDerivAt_id' x
  · -- Show that 1 ≠ 0 for x ∈ s.
    simp only [ne_eq, one_ne_zero, not_false_eq_true, eventually_true]
  · -- Show that lim log(sin x / sin a) = 0 as x tends to a.
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    rw [show 0 = log (sin a / sin a) by simp [div_self ha]]
    -- log (sin a / sin a) = log 1 = 0 and the function
    -- log (sin x / sin a) is continuous at a.
    apply ContinuousAt.tendsto
    fun_prop (disch := simpa)
  · -- Show that lim (x - a) = 0 as x tends to a.
    rw [show 0 = a - a by simp]
    apply Tendsto.sub_const
    exact tendsto_nhdsWithin_of_tendsto_nhds fun ⦃U⦄ a ↦ a
  -- (cos x / sin a) / (sin x / sin a) = cos x / sin x = cot x.
  field_simp
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  rw [show cot a = cos a / sin a by simp [cot_eq_cos_div_sin]]
  -- It is left to show that cos x / sin x is continuous at a.
  apply ContinuousAt.tendsto
  fun_prop (disch := simpa)