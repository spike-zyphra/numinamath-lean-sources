import Mathlib

/- Prove the equalities (see Leibniz triangle, problem 60424):

a) $1=1 / 2+1 / 6+1 / 12+1 / 20+1 / 30+\ldots$;

b) $1 / 2=1 / 3+1 / 12+1 / 30+1 / 60+1 / 105+\ldots$

c) $1 / 3=1 / 4+1 / 20+1 / 60+1 / 140+1 / 280+\ldots$.-/
theorem algebra_234782 :
    ∑' n : ℕ, (1 / ((n + 1) * (n + 2) : ℝ)) = 1 ∧
    ∑' n : ℕ, (1 / ((n + 1) * (n + 2) * (n + 3) / 2 : ℝ)) = 1 / 2 ∧
    ∑' n : ℕ, (1 / ((n + 1) * (n + 2) * (n + 3) * (n + 4) / 6 : ℝ)) = 1 / 3 := by
  refine ⟨?_, ?_, ?_⟩
  . -- We prove the first equality.
    suffices HasSum (fun (n : ℕ) ↦ 1 / ((n + 1) * (n + 2) : ℝ)) 1 by
      exact HasSum.tsum_eq this
    -- Now it suffices to show that the partial sums tends to 1.
    rw [hasSum_iff_tendsto_nat_of_nonneg (by intro i; positivity)]
    -- Show that ∑_{n = 0} ^ (N - 1) (1 / ((n + 1) * (n + 2) : ℝ)) = 1 - 1 / (N + 1).
    have h₀ (N : ℕ) : 1 - 1 / (N + 1) = ∑ n ∈ Finset.range N, (1 / ((n + 1) * (n + 2) : ℝ)) := by
      symm
      induction' N with N hN
      . -- Base case N = 0.
        simp
      . -- Induction step.
        rw [Finset.sum_range_succ, hN]
        field_simp
        ring
    -- Now we only need to show that 1 - 1 / (n + 1) → 1 as n → ∞.
    suffices Filter.Tendsto (fun (n : ℕ) ↦ 1 - 1 / (n + 1 : ℝ)) Filter.atTop (nhds 1) by
      apply Filter.Tendsto.congr _ this
      exact h₀
    nth_rw 4 [show (1 : ℝ) = 1 - 0 by norm_num]
    apply tendsto_const_nhds.sub
    -- We use the fact that 1 / (n + 1) → 0 as n → ∞.
    apply tendsto_one_div_add_atTop_nhds_zero_nat
  . -- We prove the second equality.
    suffices HasSum (fun (n : ℕ) ↦ 1 / ((n + 1) * (n + 2) * (n + 3) / 2 : ℝ)) (1 / 2) by
      exact HasSum.tsum_eq this
    -- Now it suffices to show that the partial sums tends to 1 / 2.
    rw [hasSum_iff_tendsto_nat_of_nonneg (by intro i; positivity)]
    -- Show that ∑_{n = 0} ^ (N - 1) (1 / ((n + 1) * (n + 2) * (n + 3) / 2 : ℝ)) = 1 / 2 - 1 / ((N + 1) * (N + 2)).
    have h₀ (N : ℕ) : 1 / 2 - 1 / ((N + 1) * (N + 2)) = ∑ n ∈ Finset.range N, (1 / ((n + 1) * (n + 2) * (n + 3) / 2 : ℝ)) := by
      symm
      induction' N with N hN
      . -- Base case N = 0.
        simp
      . -- Induction step.
        rw [Finset.sum_range_succ, hN]
        field_simp
        ring
    -- Now we only need to show that 1 / 2 - 1 / ((n + 1)(n + 2)) → 1 / 2 as n → ∞.
    suffices Filter.Tendsto (fun (n : ℕ) ↦ 1 / 2 - 1 / ((n + 1) * (n + 2) : ℝ)) Filter.atTop (nhds (1 / 2)) by
      apply Filter.Tendsto.congr _ this
      exact h₀
    nth_rw 2 [show (1 / 2 : ℝ) = 1 / 2 - 0 by norm_num]
    apply tendsto_const_nhds.sub
    rw [show (fun (n : ℕ) ↦ 1 / ((n + 1) * (n + 2) : ℝ)) = (fun x ↦ x⁻¹) ∘ ((fun x ↦ (x + 1) * (x + 2)) ∘ (fun (n : ℕ) ↦ (n : ℝ))) by ext n; simp]
    apply @Filter.Tendsto.comp _ _ _ _ _ Filter.atTop Filter.atTop
    . apply tendsto_inv_atTop_zero
    . apply @Filter.Tendsto.comp _ _ _ _ _ Filter.atTop Filter.atTop
      . apply Filter.Tendsto.atTop_mul_atTop
        all_goals
          apply Filter.tendsto_atTop_add_const_right
          apply Filter.tendsto_id
      . apply tendsto_natCast_atTop_atTop
  . -- We prove the third equality.
    suffices HasSum (fun (n : ℕ) ↦ 1 / ((n + 1) * (n + 2) * (n + 3) * (n + 4) / 6 : ℝ)) (1 / 3) by
      exact HasSum.tsum_eq this
    -- Now it suffices to show that the partial sums tends to 1 / 3.
    rw [hasSum_iff_tendsto_nat_of_nonneg (by intro i; positivity)]
    -- Show that ∑_{n = 0} ^ (N - 1) (1 / ((n + 1) * (n + 2) * (n + 3) * (n + 4) / 6 : ℝ)) = 1 / 3 - 2 / ((N + 1) * (N + 2) * (N + 3)).
    have h₀ (N : ℕ) : 1 / 3 - 2 / ((N + 1) * (N + 2) * (N + 3)) = ∑ n ∈ Finset.range N, (1 / ((n + 1) * (n + 2) * (n + 3) * (n + 4) / 6 : ℝ)) := by
      symm
      induction' N with N hN
      . -- Base case N = 0.
        norm_num
      . -- Induction step.
        rw [Finset.sum_range_succ, hN]
        field_simp
        ring
    -- Now we only need to show that 1 / 3 - 2 / ((n + 1)(n + 2)(n + 3)) → 1 / 3 as n → ∞.
    suffices Filter.Tendsto (fun (n : ℕ) ↦ 1 / 3 - 2 / ((n + 1) * (n + 2) * (n + 3) : ℝ)) Filter.atTop (nhds (1 / 3)) by
      apply Filter.Tendsto.congr _ this
      exact h₀
    nth_rw 2 [show (1 / 3 : ℝ) = 1 / 3 - 0 by norm_num]
    apply tendsto_const_nhds.sub
    rw [show (fun (n : ℕ) ↦ 2 / ((n + 1) * (n + 2) * (n + 3) : ℝ)) = (fun x ↦ 2 / x) ∘ ((fun x ↦ (x + 1) * (x + 2) * (x + 3)) ∘ (fun (n : ℕ) ↦ (n : ℝ))) by ext n; field_simp]
    apply @Filter.Tendsto.comp _ _ _ _ _ Filter.atTop Filter.atTop
    . apply Filter.Tendsto.const_div_atTop
      apply Filter.tendsto_id
    . apply @Filter.Tendsto.comp _ _ _ _ _ Filter.atTop Filter.atTop
      . iterate 2 apply Filter.Tendsto.atTop_mul_atTop
        all_goals
          apply Filter.tendsto_atTop_add_const_right
          apply Filter.tendsto_id
      . apply tendsto_natCast_atTop_atTop
