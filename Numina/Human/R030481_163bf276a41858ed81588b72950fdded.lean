import Mathlib

/- 7. Let $a, b \in \mathrm{R}$, then the minimum value of $\max \{|a+b|,|a-b|,|1-b|\}$ is

Translate the above text into English, please retain the original text's line breaks and format, and output the translation result directly. -/
theorem algebra_157874 :
    IsLeast {x : ℝ | ∃ a b, x = max (max (|a + b|) (|a - b|)) (|1 - b|)} (1 / 2) := by
      constructor
      -- a = 0, b = 1 / 2 achieves 1 / 2
      · simp only [Set.mem_setOf_eq]
        refine ⟨0, 1 / 2, ?_⟩
        simp only [one_div, zero_add, zero_sub, abs_neg, max_self]
        ring_nf
        rw [abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2) by positivity)]
        exact (max_self (1 / 2)).symm
      -- we prove that (1 / 2) is a lower bound
      · rw [mem_lowerBounds]
        simp only [Set.mem_setOf_eq, one_div, forall_exists_index]
        intro aa a b dd
        subst dd

        -- we have that |a + b| ⊔ |a - b| = |a| + |b|
        have add_eq : |a + b| ⊔ |a - b| = |a| + |b| := by
          -- |a - b| ≤ (a + b) a and b are non-negative
          have sub_abs_le_add : ∀ a' b' : NNReal, |(↑a' - ↑b' : ℝ)| ≤ ↑(a' + b') := by
            intro a' b'
            cases' le_total 0 (a' - b' : ℝ) with ha hb
            · simp only [ha, abs_of_nonneg, NNReal.coe_add, tsub_le_iff_right]
              norm_cast
              exact le_add_of_le_of_nonneg le_self_add <| zero_le b'
            · simp only [hb, abs_of_nonpos, neg_sub, NNReal.coe_add, tsub_le_iff_right]
              norm_cast
              exact le_add_of_le_of_nonneg le_add_self <| zero_le a'
          -- we split on cases of a and b
          by_cases ha : 0 ≤ a
          -- we lift to NNReal to carry information about positivity
          · lift a to NNReal using ha
            by_cases hb : 0 ≤ b
            · lift b to NNReal using hb
              norm_cast
              simp only [NNReal.abs_eq]
              simp only [NNReal.coe_add, sup_eq_left, ge_iff_le]
              norm_cast
              exact sub_abs_le_add a b
            · simp only [not_le] at hb
              rw [(neg_neg b).symm]
              lift -b to NNReal with aa bb
              · simp only [Left.nonneg_neg_iff]
                exact le_of_lt hb
              simp only [sub_neg_eq_add, NNReal.abs_eq, abs_neg]
              norm_cast
              simp only [NNReal.abs_eq]
              simp only [NNReal.coe_add, sup_eq_right, ge_iff_le]
              exact sub_abs_le_add a aa
          · rw [(neg_neg a).symm]
            lift -a to NNReal with aa bb
            · simp only [Left.nonneg_neg_iff]
              exact le_of_not_ge ha
            by_cases hb : 0 ≤ b
            · lift b to NNReal using hb
              simp only [abs_neg, NNReal.abs_eq]
              rw [←abs_neg (-↑aa - ↑b : ℝ)]
              simp only [neg_sub, sub_neg_eq_add]
              nth_rw 1 [add_comm]
              nth_rw 3 [add_comm]
              norm_cast
              simp only [NNReal.abs_eq]
              simp only [NNReal.coe_add, sup_eq_right, ge_iff_le]
              exact sub_abs_le_add b aa
            · simp only [not_le] at hb
              rw [(neg_neg b).symm]
              lift -b to NNReal with cc dd
              · simp only [Left.nonneg_neg_iff]
                exact le_of_lt hb
              rw [←abs_neg (-↑aa + -↑cc : ℝ)]
              simp only [neg_add_rev, neg_neg, sub_neg_eq_add, abs_neg, NNReal.abs_eq]
              rw [add_comm]
              norm_cast
              simp only [NNReal.abs_eq]
              simp only [NNReal.coe_add, sup_eq_left, ge_iff_le]
              rw [add_comm]
              nth_rw 2 [add_comm]
              exact sub_abs_le_add cc aa
        rw [add_eq]
        -- arithmetic mean is less than or equal to max
        have arith_le_max : ∀ x y : ℝ, (x + y) / 2 ≤ max x y := by
          intro x y
          cases' le_total x y with hx hy
          · simp only [hx, sup_of_le_right]
            linarith
          · simp only [hy, sup_of_le_left]
            linarith

        -- then we can chain inequalities (from simple to complicated)
        calc 2⁻¹
        -- a is always positive
        _ ≤ (|a| + 1) / 2 := by
          ring_nf
          simp only [one_div, le_add_iff_nonneg_right, inv_pos, Nat.ofNat_pos,
            mul_nonneg_iff_of_pos_right, abs_nonneg]
        -- 1 ≤ |b| + |1 - b|
        _ ≤ (|a| + (|b| + |1 - b|)) / 2 := by
          gcongr
          cases' le_total 0 (1 - b) with h1 h2
          · simp only [h1, abs_of_nonneg]
            cases' le_total 0 b with h3 h4
            · simp only [h3, abs_of_nonneg, add_sub_cancel, le_refl]
            · simp only [h4, abs_of_nonpos]
              rw [add_comm]
              ring_nf
              simp only [le_sub_self_iff]
              exact mul_nonpos_of_nonpos_of_nonneg h4 <| by linarith
          · simp only [h2, abs_of_nonpos]
            cases' le_total 0 b with h3 h4
            · simp only [h3, abs_of_nonneg]
              simp only [tsub_le_iff_right, zero_add] at h2
              ring_nf
              simp only [le_neg_add_iff_add_le]
              rw [mul_two]
              exact add_le_add h2 h2
            · simp only [tsub_le_iff_right, zero_add] at h2
              linarith only [h2, h4]

        -- addition is associative
        _ = ((|a| + |b|) + |1 - b|) / 2 := by ring
        -- arithmetic mean is less than or equal to max
        _ ≤ (|a| + |b|) ⊔ |1 - b| := arith_le_max _ _