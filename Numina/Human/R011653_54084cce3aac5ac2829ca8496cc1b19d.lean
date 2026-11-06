import Mathlib

open Real Filter
open scoped Topology

/- Problem condition

Calculate the limit of the function:

$\lim _{x \rightarrow \frac{\pi}{2}} \frac{2^{\cos ^{2} x}-1}{\ln (\sin x)}$ -/
theorem calculus_148203 :
    Tendsto (λ x => (2^(cos x)^2 - 1)/log (sin x)) (𝓝[≠] (π/2)) (𝓝 (-2*log 2)) := by
  -- Define s = (0, π) \ {π / 2}.
  set s := Set.Ioo 0 π \ {π / 2}
  -- Show that s ∈ 𝓝[≠] (π / 2).
  have hs : s ∈ 𝓝[≠] (π / 2) := by
    unfold s
    rw [Set.diff_eq, Set.inter_comm]
    apply inter_mem_nhdsWithin
    apply Ioo_mem_nhds <;> linarith [pi_pos]
  -- Prove that 0 < sin x for all x ∈ s.
  have hs1 {x} (hx : x ∈ s) : 0 < sin x := by
    simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
    apply sin_pos_of_pos_of_lt_pi <;> linarith
  -- Prove that cos x ≠ 0 for all x ∈ s.
  have hs2 {x} (hx : x ∈ s) : cos x ≠ 0 := by
    simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
    -- Consider two cases: x < π / 2 and π / 2 ≤ x.
    cases' lt_or_le x (π / 2) with h h
    · apply ne_of_gt
      -- If x < π / 2 then 0 < cos x for x ∈ s.
      apply cos_pos_of_mem_Ioo
      simp only [Set.mem_Ioo]
      constructor <;> linarith
    · apply ne_of_lt
      -- If π / 2 ≤ x then cos x < 0 for x ∈ s.
      apply cos_neg_of_pi_div_two_lt_of_lt _ (by linarith)
      apply lt_of_le_of_ne h (by tauto)
  -- Apply L'Hôpital's rule.
  apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => cos x * (-2 * sin x * 2^(cos x ^ 2) * log 2)) (g' := fun x => cos x / sin x)
  · rw [eventually_iff_exists_mem]
    -- Show that the derivative of 2^(cos x^2) is cos x * (-2 * sin x * 2^(cos x^2) * log 2) inside s.
    use s, hs
    intro x hx
    apply HasDerivAt.sub_const
    rw [show cos x * (-2 * sin x * 2^(cos x^2) * log 2) = 0 * cos x^2 * 2^(cos x^2 - 1) + (2 * cos x ^ (2 - 1) * (-sin x)) * 2^(cos x ^ 2) * log 2 by ring]
    apply HasDerivAt.rpow (hasDerivAt_const x 2) _ zero_lt_two
    apply HasDerivAt.pow
    exact hasDerivAt_cos x
  · rw [eventually_iff_exists_mem]
    -- Show that the derivative of log (sin x) is cos x / sin x inside s.
    use s, hs
    intro x hx
    apply HasDerivAt.log (hasDerivAt_sin x)
    exact ne_of_gt (hs1 hx)
  · rw [eventually_iff_exists_mem]
    -- Show that cos x / sin x ≠ 0 for all x ∈ s.
    use s, hs
    intro x hx
    exact div_ne_zero (hs2 hx) (ne_of_gt (hs1 hx))
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    -- Show that lim (2^cos x^2 - 1) = 0 as x tends to π / 2.
    rw [show (0 : ℝ) = 2 ^ cos (π / 2) ^ 2 - 1 by simp]
    apply ContinuousAt.tendsto
    apply ContinuousAt.sub _ continuousAt_const
    apply ContinuousAt.rpow (by fun_prop) (by fun_prop) (by norm_num)
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    -- Show that lim log (sin x) = 0 as x tends to π / 2.
    rw [show (0 : ℝ) = log (sin (π / 2)) by simp]
    apply ContinuousAt.tendsto
    fun_prop (disch := simp)
  simp_rw [div_div_eq_mul_div]
  -- It is left to prove that lim (cos x * (-2 * sin x * 2^cos x^2 * log 2) * sin x / cos x) = -2 * log 2 as x tends to π / 2.
  -- We have
  -- cos x * (-2 * sin x * 2^cos x^2 * log 2) * sin x / cos x = (-2 * sin x * 2^cos x^2 * log 2) * sin x for all x ∈ s.
  have eq : (fun x => (-2 * sin x * 2 ^ cos x ^ 2 * log 2) * sin x) =ᶠ[𝓝[≠] (π / 2)] (fun x => cos x * (-2 * sin x * 2 ^ cos x ^ 2 * log 2) * sin x / cos x) := by
    simp_rw [EventuallyEq, eventually_iff_exists_mem]
    use s, hs
    intro x hx
    field_simp [hs2 hx]
    ring
  apply Tendsto.congr' eq
  -- Show that lim ((-2 * sin x * 2^cos x^2 * log 2) * sin x) = -2 * log 2 as x tends to π / 2.
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  rw [show -2 * log 2 = (-2 * sin (π / 2) * 2 ^ cos (π / 2) ^ 2 * log 2) * sin (π / 2) by simp]
  -- It is enough to prove that (-2 * sin x * 2^cos x^2 * log 2) * sin x is
  -- continuous at π / 2.
  apply ContinuousAt.tendsto
  apply ContinuousAt.mul _ (by fun_prop)
  apply ContinuousAt.mul _ (by fun_prop)
  apply ContinuousAt.mul (by fun_prop)
  exact ContinuousAt.rpow (by fun_prop) (by fun_prop) (by norm_num)