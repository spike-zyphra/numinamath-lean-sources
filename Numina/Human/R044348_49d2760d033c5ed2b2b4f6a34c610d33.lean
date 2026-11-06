import Mathlib

open Topology Filter Real

/- ## Problem Statement
Calculate the limit of the function:
$$

\lim _{x \rightarrow \frac{\pi}{6}} \frac{\ln (\sin 3 x)}{(6 x-\pi)^{2}}

$$
 -/
theorem calculus_144021 :
    Tendsto (λ x => Real.log (Real.sin (3 * x)) / (6 * x - Real.pi) ^ 2)
    (𝓝[≠] (Real.pi / 6)) (𝓝 (-1 / 8)) := by
  -- We have log(sin(3 * x)) / (6 * x - π) ^ 2 = log(cos(3 * (x - π / 6))) / (6 * (x - π / 6))^2.
  have eq : (fun x => log (sin (3 * x)) / (6 * x - π)^2) = (fun x => log (cos (3 * x)) / (36 * x ^ 2)) ∘ (fun x => x - π / 6) := by
    ext x
    simp [mul_sub, show 3 * (π / 6) = π / 2 by ring, cos_sub_pi_div_two]
    ring_nf
  rw [eq]
  -- It is enough to show that x - π / 6 tends to 0 (but not equal to 0) as x tends to π / 6
  -- and that log(cos(3 * x)) / (36 * x^2) tends to (-1 / 8) as x tends to 0.
  apply Tendsto.comp (y := 𝓝[≠] 0)
  swap
  · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    -- Show that lim (x - π / 6) = 0 as x tends to π / 6.
    · apply Tendsto.mono_left _ nhdsWithin_le_nhds
      rw [show 0 = π / 6 - π / 6 by ring]
      apply Continuous.tendsto
      fun_prop
    -- Show that x - π / 6 ≠ 0 for all x ≠ π / 6.
    · rw [eventually_iff_exists_mem]
      use {π / 6}ᶜ
      refine ⟨self_mem_nhdsWithin, ?_⟩
      intro y hy
      simp [sub_eq_zero] at hy ⊢
      exact hy
  -- Apply L'Hôpital's rule to log(cos(3 * x)) / (36 * x^2).
  apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => -3 * sin (3 * x) / cos (3 * x)) (g' := fun x => 36 * (2 * x ^ 1))
  -- Show that the derivative of log(cos(3 * x)) is -3 * sin(3 * x) / cos(3 * x) in
  -- a neighborhood of 0 which does not include 0.
  · rw [eventually_iff_exists_mem]
    -- Consider the open interval (-π / 6, π / 6) without 0.
    use Set.Ioo (-π / 6) (π / 6) \ {0}
    constructor
    · rw [Set.diff_eq, Set.inter_comm]
      apply inter_mem_nhdsWithin
      apply Ioo_mem_nhds (by linarith [pi_pos]) (by positivity)
    · simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, neg_mul, and_imp]
      intro x hx1 hx2 hx0
      apply HasDerivAt.log
      swap
      -- We need to show that cos (3 * x) ≠ 0 for x ∈ (-π / 6, π / 6).
      · apply ne_of_gt
        apply cos_pos_of_mem_Ioo
        simp only [Set.mem_Ioo]
        constructor <;> linarith
      rw [show -(3 * sin (3 * x)) = -sin (3 * x) * (3 * 1) by ring]
      apply HasDerivAt.cos
      apply HasDerivAt.const_mul
      exact hasDerivAt_id' x
  -- Show that the derivative of 36 * x ^ 2 is 36 * (2 * x ^ 1).
  · apply Eventually.of_forall
    intro x
    apply HasDerivAt.const_mul
    apply hasDerivAt_pow
  -- Show that 36 * x ^ 2 ≠ 0 for all x ≠ 0.
  · rw [eventually_iff_exists_mem]
    use {0}ᶜ
    refine ⟨self_mem_nhdsWithin, ?_⟩
    simp
  -- Show that lim log(cos(3 * x)) = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show 0 = log (cos (3 * 0)) by simp]
    apply ContinuousAt.tendsto
    fun_prop (disch := simp)
  -- Show that lim 36 * x^2 = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show 0 = 36 * (0 : ℝ) ^ 2 by norm_num]
    apply Continuous.tendsto
    fun_prop
  field_simp
  -- We now need to compute the limit of
  -- -(3 * sin(3 * x)) / (cos (3 * x) * 72 * x) as x tends to 0.
  -- Apply L'Hôpital's rule again.
  apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => -9 * cos (3 * x)) (g' := fun x => (-sin (3 * x) * (3 * 1)) * (72 * x) + cos (3 * x) * (72 * 1))
  -- Show that the derivative of -(3 * sin(3 * x)) is -9 * cos(3 * x).
  · apply Eventually.of_forall
    intro x
    rw [show -9 * cos (3 * x) = -(3 * (cos (3 * x) * (3 * 1))) by ring]
    apply HasDerivAt.neg
    apply HasDerivAt.const_mul
    apply HasDerivAt.sin
    apply HasDerivAt.const_mul
    exact hasDerivAt_id' x
  -- Show that the derivative of cos(3 * x) * 72 * x is 72 * (cos(3 * x) - 3 * x * sin(3 * x)).
  · apply Eventually.of_forall
    intro x
    simp_rw [show ∀ x : ℝ, 36 * (2 * x) = 72 * x by intro x; ring]
    apply HasDerivAt.mul
    · apply HasDerivAt.cos
      apply HasDerivAt.const_mul
      exact hasDerivAt_id' x
    · apply HasDerivAt.const_mul
      exact hasDerivAt_id' x
  -- Show that 72 * (cos(3 * x) - 3 * x * sin(3 * x)) ≠ 0 in a neighborhood of 0.
  · simp_rw [show ∀ x, -sin (3 * x) * (3 * 1) * (72 * x) + cos (3 * x) * (72 * 1) = 72 * (cos (3 * x) - 3 * x * sin (3 * x)) by intro x; ring]
    -- It is enough to show that 0 < 72 * (cos(3 * x) - 3 * x * sin(3 * x)) in a neighborhood of 0.
    suffices ∀ᶠ (x : ℝ) in 𝓝[≠] 0, 0 < 72 * (cos (3 * x) - 3 * x * sin (3 * x)) by
      apply this.mono
      intro x h
      exact ne_of_gt h
    -- Show that lim (72 * (cos(3 * x) - 3 * x * sin(3 * x))) = 72 > 0 as x tends to 0.
    apply Tendsto.eventually_const_lt (v := 72) (by norm_num)
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show 72 = 72 * (cos (3 * 0) - 3 * 0 * sin (3 * 0)) by simp]
    apply Continuous.tendsto
    fun_prop
  -- Show that lim -(3 * sin (3 * x)) = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show 0 = -(3 * sin (3 * 0)) by simp]
    apply ContinuousAt.tendsto
    fun_prop
  -- Show that lim cos(3 * x) * 72 * x = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show 0 = cos (3 * 0) * (36 * (2 * 0)) by simp]
    apply ContinuousAt.tendsto
    fun_prop
  -- It is left to prove that lim (-9 * cos(3 * x)) / (72 * (cos(3 * x) - 3 * x * sin(3 * x))) = -1/8
  -- as x tends to 0.
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  rw [show (-1 / 8 : ℝ) = -9 * cos (3 * 0) / (-sin (3 * 0) * (3 * 1) * (72 * 0) + cos (3 * 0) * (72 * 1)) by norm_num]
  -- The function is continuous at 0 so its limit is equal to the value of the function at 0.
  apply ContinuousAt.tendsto
  fun_prop (disch := simp)