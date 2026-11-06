import Mathlib

open Topology Filter Real

/- ## Problem Statement

Calculate the limit of the function:

$\lim _{x \rightarrow 0}\left(1-\ln \left(1+x^{3}\right)\right)^{\frac{3}{x^{2} \arcsin x}}$ -/
theorem calculus_148263 :
    Tendsto (λ x => (1 - Real.log (1 + x^3))^(3 / (x^2 * Real.arcsin x))) (𝓝[≠] 0) (𝓝 (Real.exp (-3))) := by
  -- Define an auxiliary set s = (-1, 1) \ {0}.
  set s : Set ℝ := Set.Ioo (-1) 1 \ {0}
  -- Show that s ∈ 𝓝[≠] 0.
  have hs : s ∈ 𝓝[≠] 0 := by
    unfold s
    rw [Set.diff_eq, Set.inter_comm]
    apply inter_mem_nhdsWithin
    apply Ioo_mem_nhds (by norm_num) (by norm_num)
  -- Show that for all x ∈ s, 0 < 1 + x^3.
  have hs1 {x} (hx : x ∈ s) : 0 < 1 + x^3 := by
      simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
      suffices (-1)^3 < x^3 by linarith
      apply Odd.strictMono_pow (by decide) hx.1.1
  -- Show that for all x ∈ s, log (1 + x^3) < 1.
  have hs2 {x} (hx : x ∈ s) : log (1 + x ^ 3) < 1 := by
    -- It is enough to show that 1 + x^3 < exp(1).
    rw [log_lt_iff_lt_exp (hs1 hx)]
    calc
      -- 1 + x^3 ≤ 1 + 1^3 = 2 < exp(1).
      1 + x ^ 3 ≤ 1 + 1 ^ 3 := by
        apply add_le_add (le_refl _)
        apply (Odd.strictMono_pow (by decide)).monotone
        simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
        linarith
      _ < exp 1 := by linarith [Real.exp_one_gt_d9]
  -- The function from the theorem statement is equal to
  -- exp ∘ (fun x => 3 * (log (1 - log (1 + x^3)) / (x^2 * arcsin x)))
  -- in some neighborhood of 𝓝[≠] 0.
  have eq : exp ∘ (fun x => 3 * (log (1 - log (1 + x^3)) / (x^2 * arcsin x))) =ᶠ[𝓝[≠] 0] (fun x => (1 - log (1 + x^3))^(3 / (x^2 * arcsin x))) := by
    simp_rw [EventuallyEq]
    apply eventually_iff_exists_mem.mpr
    -- It is enough to show that functions are equal on s.
    use s, hs
    simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, Function.comp_apply, and_imp]
    intro x hx
    rw [rpow_def_of_pos]
    · ring_nf
    rw [sub_pos]
    exact hs2 hx
  -- Show that lim (exp ∘ (fun x => 3 * (log (1 - log (1 + x^3)) / (x^2 * arcsin x)))) is exp(-3) as x tends to 0.
  apply Tendsto.congr' eq
  clear eq
  -- exp(x) is continuous, so it is enough to show that
  -- lim (log (1 - log (1 + x^3)) / (x^2 * arcsin x)) = -1 as x tends to 0.
  apply Tendsto.comp (y := 𝓝 (-3)) (Continuous.tendsto continuous_exp _)
  rw [show (-3 : ℝ) = 3 * (-1) by norm_num]
  apply Tendsto.const_mul
  -- Apply L'Hôpital's rule to log(1 - log(1 + x^3)) / (x^2 * arcsin x).
  apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => (-(3 * x^2 / (1 + x^3))) / (1 - log (1 + x^3))) (g' := fun x => 2 * x^1 * arcsin x + x^2 * (1 / √(1 - x^2)))
  -- Show that the derivative of log(1 - log(1 + x^3)) = (-(3 * x^2 / (1 + x^3))) / (1 - log (1 + x^3))
  -- for all x ∈ s ∈ 𝓝[≠] 0.
  · rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    apply HasDerivAt.log _ (by linarith [hs2 hx])
    apply HasDerivAt.const_sub
    apply HasDerivAt.log _ (by linarith [hs1 hx])
    apply HasDerivAt.const_add
    apply hasDerivAt_pow
  -- Show that the derivative of x^2 * arcsin x = 2 * x^1 * arcsin x + x^2 * (1 / √(1 - x^2))
  -- for all x ∈ s ∈ 𝓝[≠] 0.
  · rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    apply HasDerivAt.mul (hasDerivAt_pow _ _)
    apply hasDerivAt_arcsin <;> simp [s] at hx <;> linarith
  -- Show that 2 * x^1 * arcsin x + x^2 * (1 / √(1 - x^2)) ≠ 0
  -- for all x ∈ s ∈ 𝓝[≠] 0.
  · rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
    have hx0 : x ≠ 0 := hx.2
    apply ne_of_gt
    -- It is enough to show that 0 < 2 * x * arcsin x + x^2 / √(1 - x^2) for x ∈ s.
    apply add_pos
    · rw [pow_one, mul_assoc]
      apply mul_pos zero_lt_two
      rw [mul_pos_iff, arcsin_lt_zero, arcsin_pos]
      -- 0 < x * arcsin x because x < 0 implies arcsin x < 0 and x > 0 implies arcsin x > 0.
      by_cases h : x < 0
      · right
        exact ⟨h, h⟩
      · left
        replace h : 0 < x := by
          rw [lt_iff_le_and_ne]
          exact ⟨by linarith, Ne.symm hx0⟩
        exact ⟨h, h⟩
    · simp
      -- 0 < x^2 / √(1 - x^2) because x ∈ (-1, 1) and x ≠ 0.
      apply mul_pos (by positivity)
      rw [inv_pos, sqrt_pos, sub_pos, show (1 : ℝ) = 1 ^ 2 by norm_num]
      rw [sq_lt_sq]
      norm_num
      rw [abs_lt]
      exact hx.1
  -- Show that lim log(1 - log(1 + x^3)) = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show (0 : ℝ) = log (1 - log (1 + 0 ^ 3)) by simp]
    -- The result follows from the fact that log(1 - log(1 + x^3)) is continuous at 0.
    apply ContinuousAt.tendsto
    fun_prop (disch := norm_num)
  -- Show that lim x^2 * arcsin x = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show (0 : ℝ) = 0 ^ 2 * arcsin 0 by simp]
    -- The result follows from the fact that x^2 * arcsin x is continuous at 0.
    apply ContinuousAt.tendsto
    apply ContinuousAt.mul (by fun_prop) continuousAt_arcsin
  -- For all x ∈ s, we have
  -- -(3 * x ^ 2 / (1 + x ^ 3)) / (1 - log (1 + x ^ 3)) / (2 * x ^ 1 * arcsin x + x ^ 2 * (1 / √(1 - x ^ 2)))
  --   = -1 * (3 / ((1 + x^3) * (1 - log (1 + x^3)) * (2 * (arcsin x / x) + 1 / √(1 - x^2)))).
  have eq : (fun x => -1 * (3 / ((1 + x^3) * (1 - log (1 + x^3)) * (2 * (arcsin x / x) + 1 / √(1 - x^2)))))
      =ᶠ[𝓝[≠] 0] (fun x ↦ -(3 * x ^ 2 / (1 + x ^ 3)) / (1 - log (1 + x ^ 3)) / (2 * x ^ 1 * arcsin x + x ^ 2 * (1 / √(1 - x ^ 2)))) := by
    simp_rw [EventuallyEq, eventually_iff_exists_mem]
    use s, hs
    intro x hx
    simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
    field_simp [hx.2]
    rw [show 2 * x * arcsin x + x ^ 2 / √(1 - x^2) = x * (2 * arcsin x + x / √(1 - x^2)) by ring]
    have h a b c : -(3 * x^2) / (a * b * (x * c)) = -(3 * x) / (a * b * c) := by
      rw [show 3 * x^2 = x * (3 * x) by ring]
      rw [show a * b * (x * c) = x * (a * b * c) by ring]
      rw [neg_div, neg_div, mul_div_mul_left _ _ hx.2]
    rw [h]
  apply Tendsto.congr' eq
  -- To find the limit of -1 * (3 / ((1 + x^3) * (1 - log (1 + x^3)) * (2 * (arcsin x / x) + 1 / √(1 - x^2))))
  -- as x tends to 0, observe that all subexpressions are continuous functions at x = 0
  -- except arcsin x / x.
  -- It is enough to show that arcsin x / x tends to 1 as x tends to 0.
  nth_rw 2 [show (-1 : ℝ) = -1 * (3 / ((1 + 0^3) * (1 - log (1 + 0^3)) * (2 * 1 + 1 / √(1 - 0^2)))) by norm_num]
  apply Tendsto.const_mul
  apply Tendsto.div tendsto_const_nhds _ (by norm_num)
  apply Tendsto.mul
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ContinuousAt.tendsto
    fun_prop (disch := norm_num)
  apply Tendsto.add
  swap
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ContinuousAt.tendsto
    fun_prop (disch := norm_num)
  apply Tendsto.const_mul
  -- Apply L'Hôpital's rule to arcsin x / x.
  apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => 1 / √(1 - x^2)) (g' := fun x => 1)
  -- Show that the derivative of arcsin x = 1 / √(1 - x^2) for all x ∈ s.
  · rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
    apply hasDerivAt_arcsin <;> linarith
  -- The derivative of x is 1 for all x.
  · simp only [hasDerivAt_id', eventually_true]
  -- 1 ≠ 0.
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, eventually_true]
  -- lim arcsin(x) = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show (0 : ℝ) = arcsin 0 by simp]
    apply Continuous.tendsto
    exact continuous_arcsin
  -- lim x = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact fun ⦃U⦄ a ↦ a
  -- 1 / √(1 - x^2) is continuous at 0, so its limit is 1 at 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 4 [show (1 : ℝ) = 1 / √(1 - 0^2) / 1 by norm_num]
    apply ContinuousAt.tendsto
    fun_prop (disch := norm_num)