import Mathlib

open Real

/- 11. Let $n$ positive numbers $a_{1}, a_{2}, \cdots, a_{n}$ satisfy $a_{1}+a_{2}+\cdots+a_{n}=2023, M$ be

$$

\frac{a_{1}}{2023+a_{1}}, \frac{a_{2}}{2023+a_{1}+a_{2}}, \cdots, \frac{a_{n}}{2023+a_{1}+a_{2}+\cdots+a_{n}}

$$


the maximum value among these, then the minimum possible value of $M$ is $\qquad$ . -/
theorem inequalities_258444 (n : ℕ) (hn : 0 < n) :
    IsLeast
      ((fun a => (Finset.univ.image (fun i : Fin n => (a i / (2023 + ∑ j ∈ Finset.Iic i, a j) : ℝ))).max  )
        '' {a : Fin n → ℝ | ∑ i : Fin n, a i = 2023 ∧ ∀ i, 0 < a i}) ((1 - 1 / (2 ^ (1 / (n : ℝ)))) : ℝ)
  := by
    -- n is not zero
    have : NeZero n := NeZero.of_pos hn
    have n_real_ne_zero : (n : ℝ) ≠ 0 := by
      norm_cast
      exact Nat.not_eq_zero_of_lt hn

    constructor
    -- we have a value that acheives the minimum, (1 - 1 / 2 ^ (1 / n)
    · simp only [one_div, Set.mem_image, Set.mem_setOf_eq]
      refine ⟨?_, ?_⟩
      intro ⟨k, kh⟩
      -- it achieves the minimum when a_k = 2023 * ((2 ^ (1 / n)) ^ (k + 1) - (2 ^ (1 / n)) ^ k)
      exact 2023 * ((2 ^ ((1 : ℝ) / n)) ^ (k + 1) - (2 ^ ((1 : ℝ) / n)) ^ k)
      refine ⟨?_, ?_⟩
      · simp only [one_div]
        refine ⟨?_, ?_⟩
        -- sum of a_1, .., a_n is equal to 2023
        -- 2023 constant distributes over sum
        · rw [←Finset.mul_sum]
          -- cancel 2023
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀]

          -- sum over range of ℕ instead of Fin n
          rw [Finset.sum_fin_eq_sum_range]

          -- simplify by removing if then else in sum
          convert_to (∑ x ∈ Finset.range n, (((2 : ℝ) ^ (↑n : ℝ)⁻¹) ^ (x + 1) - ((2 : ℝ) ^ (↑n : ℝ)⁻¹) ^ x)) = 1
          · apply Finset.sum_congr rfl
            intro x xh
            simp only [Finset.mem_range.mp xh, reduceDIte]

          -- Simplify telescoping sum
          rw [Finset.sum_range_sub]
          simp only [pow_zero]
          rw [←Real.rpow_natCast, ←Real.rpow_mul (by positivity), inv_mul_cancel₀ n_real_ne_zero]
          ring

        -- every a_k is positive
        · intro i
          simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, sub_pos]
          rw [←Real.rpow_natCast, ←Real.rpow_natCast]

          -- 1 < 2 ^ (n⁻¹)
          have one_lt_two_pow : (1 : ℝ) < 2 ^ (n : ℝ)⁻¹ := by
            refine one_lt_rpow ?_ ?_
            -- because 1 < 2
            linarith only
            -- and (n⁻¹) is positive
            positivity

          -- power operation is monotone in the exponent
          rw [Real.rpow_lt_rpow_left_iff one_lt_two_pow]

          -- i < i + 1
          norm_num

      -- then we prove that the values have a maximum of (1 - 1 / 2 ^ (1 / n)
      simp only [one_div, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_mk]

      -- Only consider real numbers, nothing here is ⊥
      rw [←Finset.coe_max']
      simp only [WithBot.coe_inj]

      -- the maximum is (1 - 1 / 2 ^ (1 / n), because every value is (1 - 1 / 2 ^ (1 / n)
      apply Finset.sup'_eq_of_forall

      -- simplify
      simp only [Finset.mem_image, Finset.mem_univ, true_and, id_eq, forall_exists_index,
        forall_apply_eq_imp_iff]

      intro a

      -- the finite set of Fin n less than a is equal to a finite set of natural numbers, mapped to Fin n
      have fin_bounded_as_image : Finset.Iic a = (Finset.range (a + 1)).image (Fin.ofNat' n) := by
        ext x
        simp only [Finset.mem_Iic, Finset.mem_image, Finset.mem_range, Fin.ofNat'_eq_cast]
        constructor
        · intro hh
          refine ⟨x.1, ?_⟩
          exact ⟨Order.lt_add_one_iff.mpr hh, Fin.cast_val_eq_self x⟩
        · simp only [forall_exists_index, and_imp]
          intro aa bb cc
          subst cc
          suffices cast_eq : ((aa : Fin n) : ℕ) ≤ a
          · exact cast_eq
          simp only [Fin.val_natCast]
          convert_to aa ≤ ↑a
          · refine Nat.mod_eq_of_lt <| Nat.lt_of_lt_of_le bb a.2
          exact Nat.le_of_lt_succ bb
      rw [fin_bounded_as_image]

      -- let f be the function we're summing over
      let f := (fun xx => (2023 * ((2 ^ (↑n : ℝ)⁻¹) ^ (xx + 1) - ((2 : ℝ) ^ (↑n : ℝ)⁻¹) ^ xx)))

      -- then the sum over f with Fin n can be replaced by sum over range of natural numbers
      have sum_fin_eq_nat : ∑ x ∈ (Finset.range (↑a + 1)).image (Fin.ofNat' n), f x
        = ∑ x ∈ (Finset.range (↑a + 1)), f x := by
        rw [Finset.sum_image]
        apply Finset.sum_congr rfl
        simp only [Finset.mem_range, Fin.ofNat'_eq_cast, Fin.val_natCast]
        intro aa bb
        congr
        refine Nat.mod_eq_of_lt ?_
        exact Nat.lt_of_lt_of_le bb a.2
        intro aa bb cc dd ee
        simp only [Fin.ofNat', Fin.mk.injEq] at ee
        simp only [Finset.mem_range] at bb dd
        convert ee
        refine (Nat.mod_eq_of_lt ?_).symm
        exact Nat.lt_of_lt_of_le bb a.2
        refine (Nat.mod_eq_of_lt ?_).symm
        exact Nat.lt_of_lt_of_le dd a.2
      rw [sum_fin_eq_nat]

      -- simplify telescoping sum
      rw [←Finset.mul_sum, Finset.sum_range_sub, ←mul_one_add, mul_div_mul_left]

      -- routine algebra
      simp only [pow_zero, add_sub_cancel]
      rw [sub_div, div_self]
      congr
      rw [←Real.rpow_natCast, ←Real.rpow_natCast, ←(rpow_sub' ?_ ?_)]
      simp only [Nat.cast_add, Nat.cast_one, sub_add_cancel_left]
      exact rpow_neg_one _
      -- we used that 0 ≤ 2 ^ (↑n)⁻¹
      · positivity
      -- we used that a - (a + 1) ≠ 0
      · simp only [Nat.cast_add, Nat.cast_one, sub_add_cancel_left, ne_eq, neg_eq_zero, one_ne_zero,
          not_false_eq_true]
      -- we used that (2 ^ (↑n)⁻¹) ^ (↑a + 1) ≠ 0
      · simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
          pow_eq_zero_iff, Nat.ofNat_nonneg]
        positivity
      -- we used that 2023 ≠ 0
      · linarith only
      -- the set is nonempty, because it's the image of a nonempty set
      · simp only [Finset.image_nonempty]
        -- so the set of all Fin n is nonempty
        exact Finset.univ_nonempty

    -- we prove that (1 - 1 / 2 ^ (1 / n)) is a lower bound
    · rw [mem_lowerBounds]
      simp only [Set.mem_image, Set.mem_setOf_eq, one_div, forall_exists_index, and_imp]
      intro _ a r lt wow
      subst wow

      -- let M be the maximum value
      let M : ℝ := by
        refine (Finset.image (fun i : Fin n => (a i : ℝ) / (2023 + ∑ j ∈ Finset.Iic i, (a j : ℝ))) Finset.univ).max' ?_
        -- the maximum exists because the set is nonempty
        exact Finset.image_nonempty.mpr Finset.univ_nonempty

      -- we're gonna show 1 - 1 / 2 ^ (1 / n) ≤ M
      convert_to (((1 : ℝ) - ((2 : ℝ) ^ (n : ℝ)⁻¹)⁻¹) : WithBot ℝ) ≤ (M : WithBot ℝ)
      · exact (Finset.coe_max' _).symm

      -- Everything is in ℝ, nothing is ⊥
      simp only [WithBot.coe_le_coe]

      -- Let x be an extension of a to all naturals
      let x : ℕ → ℝ := fun k => 2023 + ∑ i ∈ Finset.range k, if hh : i < n then a ⟨i, hh⟩ else 0

      -- x 0 = 2023
      have x_zero : x 0 = 2023 := by
        unfold x
        simp only [add_right_eq_self]
        exact Finset.sum_empty

      -- x n = 4046
      have x_n : x n = 4046 := by
        unfold x
        convert_to _ = (2023 : ℝ) + 2023
        · ring
        simp only [add_right_inj]
        rw [←r]
        rw [Finset.sum_range]
        congr
        ext ii
        simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]

      -- a_i = x_(i+1) - x_i
      have a_eq : ∀ i : Fin n, a i = x (i + 1) - x i := by
        intro i
        unfold x
        simp only [add_sub_add_left_eq_sub]
        rw [←Finset.sum_sdiff_eq_sub, Finset.range_succ, Finset.insert_sdiff_cancel]
        simp only [Finset.sum_singleton, Fin.is_lt, ↓reduceDIte, Fin.eta]
        exact Finset.not_mem_range_self
        refine Finset.range_subset.mpr ?_
        exact Nat.le_add_right i 1

      -- let f_k be one of the values which we have taken the maximum of
      let f := fun i : Fin n => a i / ((2023 : ℝ) + ∑ j ∈ Finset.Iic i, a j)

      -- then M (the maximum) is larger than every f_k
      have M_le : ∀ k : Fin n, f k ≤ M := by
        unfold M f
        intro k
        apply Finset.le_max'
        simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_apply_eq_apply]

      -- We can express a sum over Fin n as a sum over natural numbers
      have as_nat : ∀ (k : Fin n), ∑ j ∈ Finset.Iic k, a j
        = ∑ x ∈ Finset.range (k.1 + 1), if h : x < n then a ⟨x, h⟩ else 0 := by
          intro k
          refine Finset.sum_bij_ne_zero ?_ (fun a' => ?_) ?_ ?_ ?_
          · intro aa bb cc
            exact aa.1
          · simp only [Finset.mem_Iic, ne_eq, Finset.mem_range]
            omega
          · intro aa bb cc dd ee ff gg
            exact Fin.eq_of_val_eq gg
          · intro aa bb cc
            have ⟨k, kh⟩ := k
            simp only [Finset.mem_range] at bb
            refine ⟨⟨aa, lt_of_lt_of_le bb kh⟩, ?_⟩
            simp only [ne_eq, exists_prop, and_true, Finset.mem_Iic, Fin.mk_le_mk]
            refine ⟨?_, ?_⟩
            · exact Nat.le_of_lt_succ bb
            · exact ne_of_gt (lt _)
          · intro aa bb cc
            simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]

      -- we have f_k = (x_(k + 1) - x_k) / x_(k + 1)
      have f_k_eq : ∀ k : Fin n, f k = ((x (k + 1)) - (x k)) / (x (k + 1)) := by
        intro k
        unfold f
        congr 1
        · exact a_eq k
        · unfold x
          simp only [add_right_inj]
          exact as_nat k

      -- x is monotone
      have x_mono : Monotone x := by
        intro aa bb cc
        unfold x
        simp only [add_le_add_iff_left]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        refine Finset.range_subset.mpr cc
        intro dd ee ff
        split_ifs with hh
        · exact le_of_lt <| lt ⟨dd, hh⟩
        · exact le_refl 0

      -- x is never zero
      have x_ne_zero : ∀ k, x k ≠ 0 := by
        intro k
        have x_zero_le : x 0 ≤ x k := by
          apply x_mono
          omega
        have lt_x_zero : 0 < x 0 := by linarith only [x_zero]

        have ltt : 0 < x k := lt_of_lt_of_le lt_x_zero x_zero_le
        exact (ne_of_lt ltt).symm

      -- we have 1 - M ≤ x_k / x_k(k + 1)
      have bound_M : ∀ k : Fin n, 1 - M ≤ (x k) / x (k + 1) := by
        intro k
        have f_k_le_M := M_le k
        rw [f_k_eq k, sub_div] at f_k_le_M
        have yeo : x (k + 1) ≠ 0 := x_ne_zero (k + 1)
        have eq_one : x (k + 1) / x (k + 1) = 1 := (div_eq_one_iff_eq yeo).mpr rfl
        rw [eq_one] at f_k_le_M
        linarith only [f_k_le_M]

      -- We have an upper bound on M: 0 ≤ 1 - M
      have M_bound : 0 ≤ 1 - M := by
        unfold M
        simp only [sub_nonneg, Finset.max'_le_iff, Finset.mem_image, Finset.mem_univ,
          true_and, forall_exists_index, forall_apply_eq_imp_iff]
        intro aa
        refine (div_le_one₀ ?_).mpr ?_
        suffices hh : 0 ≤ ∑ j ∈ Finset.Iic aa, a j
        · exact Right.add_pos_of_pos_of_nonneg (by linarith only) hh
        apply Finset.sum_nonneg
        · intro _ _
          exact le_of_lt (lt _)
        · rw [←Finset.add_sum_Iio_eq_sum_Iic]
          suffices h : 0 ≤ ∑ x ∈ Finset.Iio aa, a x
          · linarith only [h]
          apply Finset.sum_nonneg
          intro _ _
          exact le_of_lt (lt _)

      -- so then we have that (1 - M) ^ n ≤ ∏ k ∈ [0, n), x k / x (k + 1)
      have M_prod_bound : (1 - M) ^ n ≤ ∏ k ∈ Finset.range n, x k / x (k + 1) := by
        nth_rw 1 [←Finset.card_range n]
        rw [←Finset.prod_const]
        apply Finset.prod_le_prod
        intro i ih
        exact M_bound
        intro k kh
        simp only [Finset.mem_range] at kh
        exact bound_M ⟨k, kh⟩

      -- If we have a telescoping product where the function is never 0, then we can simplify the product
      have tele_r : ∀ {f : ℕ → ℝ} {m}, (∀ k, f k ≠ 0)
        → ∏ k ∈ Finset.range m, f k / f (k + 1) = f 0 / f m := by
          intro f m fh
          induction' m with h1 h2
          · simp only [Finset.range_zero, Finset.prod_div_distrib, Finset.prod_empty, ne_eq,
            one_ne_zero, not_false_eq_true, div_self]
            exact (div_self <| fh 0).symm
          · rw [Finset.prod_range_succ]
            have subs := Finset.range_subset.mpr <| Nat.le_add_right h1 1
            rw [h2]
            apply div_mul_div_cancel₀
            exact fh h1

      -- We can simplify our telescoping product, it equals 1 / 2
      have x_div : x 0 / x n = 1 / 2 := by
        rw [x_zero, x_n]
        linarith only
      rw [tele_r x_ne_zero, x_div] at M_prod_bound

      -- isolate M on RHS of inequality
      have final_le : ((1 - M) ^ n) ^ ((n : ℝ)⁻¹) ≤ (1 / 2) ^ ((n : ℝ)⁻¹) := by
        refine (Real.rpow_le_rpow_iff ?_ ?_ ?_).mpr M_prod_bound
        all_goals positivity
      rw [←rpow_natCast, Real.rpow_rpow_inv, tsub_le_iff_tsub_le] at final_le

      -- left hand sides of the inequalities are equal
      have lhs_eq : 1 - (1 / 2) ^ (n : ℝ)⁻¹ = (1 - (2 ^ (n : ℝ)⁻¹)⁻¹ : ℝ) := by
        simp only [one_div]
        rw [Real.inv_rpow]
        positivity

      -- so they're equal
      exact lhs_eq ▸ final_le

      · exact M_bound
      · simp only [ne_eq, Nat.cast_eq_zero]
        exact Nat.not_eq_zero_of_lt hn