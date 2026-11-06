import Mathlib

open Topology Filter Real

/- ## Problem Statement

Calculate the limit of the function:

$\lim _{x \rightarrow a} \frac{a^{\left(x^{2}-a^{2}\right)}-1}{\tan \ln \left(\frac{x}{a}\right)}$ -/
theorem calculus_142522 {a : ℝ} (ha : 0 < a) :
    Tendsto (λ x => (a ^ (x ^ 2 - a ^ 2) - 1) / tan (log (x / a))) (𝓝[≠] a) (𝓝 (2 * a ^ 2 * log a)) := by
  -- Prove an auxiliary lemma:
  -- the derivative of a^f(x) is a^f(x) * log a * f'(x).
  have rpow_deriv {f f' : ℝ → ℝ} {x : ℝ} (h : HasDerivAt f (f' x) x) : HasDerivAt (fun x => a ^ f x) (a ^ f x * log a * f' x) x := by
    apply HasDerivAt.comp _ _ h
    apply HasStrictDerivAt.hasDerivAt
    apply hasStrictDerivAt_const_rpow ha
  -- Define s = (a / 2, 2 * a) \ {a}.
  set s := Set.Ioo (a / 2) (2 * a) \ {a}
  -- We have s ∈ 𝓝[≠] a.
  have hs : s ∈ 𝓝[≠] a := by
    unfold s
    rw [Set.diff_eq, Set.inter_comm]
    apply inter_mem_nhdsWithin
    apply Ioo_mem_nhds (by linarith) (by linarith)
  -- Show that x ∈ s implies that 1 / 2 < x / a < 2.
  have hxs {x} (hx : x ∈ s) : 1 / 2 < x / a ∧ x / a < 2 := by
    simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
    constructor
    · rw [lt_div_iff₀ ha]
      linarith
    · rw [div_lt_iff₀ ha]
      linarith
  -- Show that x ∈ s implies that 0 < cos (log (x / a)).
  have hs_cos {x} (hx : x ∈ s) : 0 < cos (log (x / a)) := by
    have ⟨hx1, hx2⟩ := hxs hx
    apply cos_pos_of_mem_Ioo
    simp only [Set.mem_Ioo]
    -- It is enough to show that -(π / 2) < log (x / a) < π / 2.
    -- The result follows from -(π / 2) < -log 2 = log (1 / 2) < log (x / a) < log 2 < π / 2.
    constructor
    · trans log (1 / 2)
      · simp
        linarith [log_two_lt_d9, pi_gt_d2]
      · apply strictMonoOn_log (by simp) (by simp; linarith) hx1
    · trans log 2
      · apply strictMonoOn_log (by simp; linarith) (by simp) hx2
      · linarith [log_two_lt_d9, pi_gt_d2]
  -- Apply L'Hôpital's rule to compute the limit.
  apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => a ^ (x ^ 2 - a ^ 2) * log a * (2 * x)) (g' := fun x => 1 / cos (log (x / a)) ^ 2 * ((1 / a) / (x / a)))
  · rw [eventually_iff_exists_mem]
    -- Show that the derivative of a ^ (x ^ 2 - a ^ 2) - 1 is a ^ (x ^ 2 - a ^ 2) * log a * (2 * x) for x ∈ s.
    use s, hs
    intro x hx
    apply HasDerivAt.sub_const
    apply rpow_deriv
    apply HasDerivAt.sub_const
    rw [show 2 * x = 2 * x ^ (2 - 1) by ring]
    apply hasDerivAt_pow
  · rw [eventually_iff_exists_mem]
    -- Show that the derivative of tan(log(x / a)) is 1 / cos (log (x / a)) ^ 2 * (1 / a / (x / a)) for x ∈ s.
    use s, hs
    intro x hx
    apply @HasDerivAt.comp (h₂ := tan) (h := fun x => log (x / a))
    · apply Real.hasDerivAt_tan
      apply ne_of_gt
      exact hs_cos hx
    · apply HasDerivAt.log _ (by linarith [hxs hx])
      apply HasDerivAt.div_const
      exact hasDerivAt_id' x
   -- Show that 1 / cos (log (x / a)) ^ 2 * (1 / a / (x / a)) ≠ 0 for x ∈ s.
  · rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    apply ne_of_gt
    apply mul_pos
    · have := hs_cos hx
      positivity
    · have := (hxs hx).1
      positivity
  -- Show that lim (a^(x^2 - a^2) - 1) = 0 as x tends to a.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    rw [show (0 : ℝ) = a ^ (a ^ 2 - a ^ 2) - 1 by simp]
    apply ContinuousAt.tendsto
    apply ContinuousAt.sub _ (by fun_prop)
    apply ContinuousAt.rpow (by fun_prop) (by fun_prop) (by left; linarith)
  -- Show that lim (tan(log(x / a))) = 0 as x tends to a.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    rw [show (0 : ℝ) = tan (log (a / a)) by simp [div_self (ne_of_gt ha)]]
    apply ContinuousAt.tendsto
    apply ContinuousAt.comp (g := tan)
    · simp [div_self (ne_of_gt ha), continuousAt_tan]
    · apply ContinuousAt.log (by fun_prop) (by positivity)
  -- It is left to show that the limit of
  -- a ^ (x ^ 2 - a ^ 2) * log a * (2 * x) / (1 / cos (log (x / a)) ^ 2 * (1 / a / (x / a)))
  -- is equal to 2 * a^2 * log a as x tends to a.
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  have ha1 : a / a = 1 := by simp [div_self (ne_of_gt ha)]
  have eq : 2 * a ^ 2 * log a = (a ^ (a^2 - a^2) * log a * (2 * a)) / (1 / cos (log (a / a)) ^ 2 * (1 / a / (a / a))) := by
    simp [ha1]
    ring
  rw [eq]
  -- It is enough to show that the function is continuous at a.
  apply ContinuousAt.tendsto
  apply ContinuousAt.div
  · apply ContinuousAt.mul _ (by fun_prop)
    apply ContinuousAt.mul _ (by fun_prop)
    apply ContinuousAt.rpow (by fun_prop) (by fun_prop) (by left; linarith)
  · apply ContinuousAt.mul _ (by fun_prop (disch := simp [ha1]))
    apply ContinuousAt.div (by fun_prop) (by fun_prop (disch := simp [ha1])) (by simp [ha1])
  · simp [ha1, ne_of_gt ha]