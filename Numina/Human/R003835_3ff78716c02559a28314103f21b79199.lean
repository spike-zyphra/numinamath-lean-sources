import Mathlib

/- Conversion from reals to non-negative reals commutes with supremum of a function if the function is non-negative. -/
lemma NNReal_iSup_map_ofReal {I : Type*} [Nonempty I]
  {f : I → ℝ} (fh : ∀ i, 0 ≤ f i)
  : ⨆ i, (f i).toNNReal = (⨆ i, f i).toNNReal := by
    rw [←NNReal.coe_inj, NNReal.coe_iSup, Real.coe_toNNReal']

    have sup_zero : (⨆ i, f i) ⊔ 0 = ⨆ i, f i
      := sup_eq_left.mpr <| Real.iSup_nonneg fh

    rw [sup_zero]
    exact iSup_congr (max_eq_left <| fh ·)

/- Conversion from reals to extended non-negative reals commutes with supremum of a function if the function is non-negative. -/
lemma ENNReal_iSup_map_ofReal {I : Type*} [Fintype I] [Nonempty I]
  {f : I → ℝ} (fh : ∀ i, 0 ≤ f i)
  : ⨆ i, ENNReal.ofReal (f i) = ENNReal.ofReal (⨆ i, f i) := by
    convert_to ⨆ i, ENNReal.ofNNReal ((f i).toNNReal) = ENNReal.ofNNReal (⨆ i, f i).toNNReal
    rw [←ENNReal.coe_iSup]
    congr
    exact NNReal_iSup_map_ofReal fh
    norm_num

/- If a function is positive, the supremum of the function can be considered as an extended non-negative real. -/
lemma real_iSup_nonneg_eq_ennreal_ofreal {I : Type*} [Fintype I] [Nonempty I]
  {f : I → ℝ} (fh : ∀ i, 0 < f i) (s : ℝ)
  : s = ⨆ i, f i ↔ ENNReal.ofReal s = ⨆ i, ENNReal.ofReal (f i) := by
    rw [ENNReal_iSup_map_ofReal (le_of_lt <| fh ·)]
    constructor
    · aesop
    · intro aa
      obtain ⟨i, hi⟩ : ∃ i, f i = ⨆ i, f i := exists_eq_ciSup_of_finite
      rw [←hi] at aa ⊢
      have left_pos : 0 < ENNReal.ofReal (f i) := ENNReal.ofReal_pos.mpr (fh i)
      have right_pos : 0 < ENNReal.ofReal s := aa ▸ left_pos
      have right_pos' : 0 < s := ENNReal.ofReal_pos.mp right_pos

      refine (ENNReal.ofReal_eq_ofReal_iff ?_ ?_).mp aa
      · exact le_of_lt right_pos'
      · exact le_of_lt (fh i)

/- Inverse of infimum is equal to supremum of inverses, given all positive -/
lemma real_inv_iInf {I : Type*} [Fintype I] [Nonempty I]
  {f : I → ℝ} (h : ∀ i, 0 < f i)
  : (⨅ i, f i)⁻¹ = ⨆ i, (f i)⁻¹ := by
    refine (real_iSup_nonneg_eq_ennreal_ofreal ?_ (⨅ i, f i)⁻¹).mpr ?_
    · norm_num
      exact h
    · have inf_pos : 0 < ⨅ i, f i := by
        obtain ⟨i, hi⟩ : ∃ i, f i = ⨅ i, f i := exists_eq_ciInf_of_finite
        exact hi ▸ h i
      rw [ENNReal.ofReal_inv_of_pos inf_pos]
      have left_eq : ⨆ i, ENNReal.ofReal (f i)⁻¹ = ⨆ i, (ENNReal.ofReal (f i))⁻¹ := by
        congr
        ext i
        rw [ENNReal.ofReal_inv_of_pos]
        exact h i
      rw [left_eq]

      rw [←ENNReal.inv_iInf]
      exact inv_inj.mpr <| ENNReal.ofReal_iInf f

/- Inverse of supremum is equal to infimum of inverses, given all positive. -/
lemma real_inv_iSup {I : Type*} [Fintype I] [Nonempty I]
  {f : I → ℝ} (h : ∀ i, 0 < f i)
  : (⨆ i, f i)⁻¹ = ⨅ i, (f i)⁻¹ := by
    norm_num [←inv_inj, real_inv_iInf (inv_pos_of_pos <| h ·)]

/- A real number is the supremum of a sequence iff it's inverse is equal to the infimum of inverses of sequence. -/
lemma real_inv_iInf_iff {I : Type*} [Fintype I] [Nonempty I]
  {f : I → ℝ} (h : ∀ i, 0 < f i) (s : ℝ)
  : s = ⨆ i, f i ↔ s⁻¹ = ⨅ i, (f i)⁻¹ := by
    simpa only [←real_inv_iSup h] using Iff.symm inv_inj

/- A real number is the infimum of a sequence iff it's inverse is equal to the supremum of inverses of sequence. -/
lemma real_inv_iSup_iff {I : Type*} [Fintype I] [Nonempty I]
  {f : I → ℝ} (h : ∀ i, 0 < f i) (s : ℝ)
  : s = ⨅ i, f i ↔ s⁻¹ = ⨆ i, (f i)⁻¹ := by
    simpa only [←real_inv_iInf h] using Iff.symm inv_inj

/- Addition of a constant commutes with supremum -/
lemma real_iSup_add {I : Type*} [Fintype I] [Nonempty I]
  (f : I → ℝ) (a : ℝ)
  : (⨆ i, f i) + a = ⨆ i, (f i + a) := ciSup_add (Finite.bddAbove_range f) a

/- Addition of a constant commutes with infimum -/
lemma real_iInf_add {I : Type*} [Fintype I] [Nonempty I]
  (f : I → ℝ) (a : ℝ)
  : (⨅ i, f i) + a = ⨅ i, (f i + a) := ciInf_add (Finite.bddBelow_range f) a

/- A real number is the supremum of a sequence iff adding a constant is equal to the supremum of the sequence with the constant added. -/
lemma real_add_iSup_iff {I : Type*} [Fintype I] [Nonempty I]
  (f : I → ℝ) (a : ℝ) (s : ℝ)
  : s = ⨆ i, f i ↔ s + a = ⨆ i, (f i + a) := by
    simpa only [←real_iSup_add] using add_right_cancel_iff.symm

/- A real number is the infimum of a sequence iff adding a constant is equal to the infimum of the sequence with the constant added. -/
lemma real_add_iInf_iff {I : Type*} [Fintype I] [Nonempty I]
  (f : I → ℝ) (a : ℝ) (s : ℝ)
  : s = ⨅ i, f i ↔ s + a = ⨅ i, (f i + a) := by
    simpa only [←real_iInf_add] using add_right_cancel_iff.symm

/- The product of a nonnegative sequence is less than or equal to a product of copies of the supremum of the sequence. -/
lemma Fintype_prod_le_prod_iSup_of_nonneg {I : Type*} [Fintype I]
  {f : I → ℝ} (h : ∀ i, 0 ≤ f i)
  : ∏ i, f i ≤ ∏ _ : I, ⨆ j, f j := by
    refine Finset.prod_le_prod ?_ ?_
    · norm_num [h]
    · norm_num [le_ciSup (Finite.bddAbove_range f)]

/- The values that are less than four is {0, 1, 2, 3}. -/
lemma Fin_univ_four : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide

/- 1. Given the positive real numbers $x_{1}, x_{2}, x_{3}$, and $x_{4}$ such that


$$

x_{1}+x_{2}+x_{3}+x_{4}=1

$$


Let $s$ be the largest of the numbers


$$

\frac{x_{1}}{1+x_{1}}, \frac{x_{2}}{1+x_{1}+x_{2}}, \frac{x_{3}}{1+x_{1}+x_{2}+x_{3}}, \frac{x_{4}}{1+x_{1}+x_{2}+x_{3}+x_{4}}

$$


What is the smallest value that $s$ can achieve? -/
theorem inequalities_215188 :
    IsLeast {s | ∃ x : Fin 4 → ℝ, (∀ i, 0 < x i) ∧ (∑ i, x i = 1) ∧
      s = ⨆ i, x i / (1 + ∑ j with j ≤ i, x j)} (1 - 1 / 2 ^ ((1 : ℝ) / 4)) := by

      -- let f be the four elements we're taking the maximum of
      set f := fun (x : Fin 4 → ℝ) i => x i / (1 + ∑ j with j ≤ i, x j)

      convert_to IsLeast {s | ∃ x : Fin 4 → ℝ, (∀ i, 0 < x i) ∧ ∑ i, x i = 1 ∧ s = ⨆ i, f x i} _

      -- every element of f is positive
      have f_pos : ∀ x i, (∀ i, 0 < x i) → 0 < f x i := by
        intro x i h
        unfold f
        apply div_pos
        exact h i
        trans 1 + 0
        · linarith
        gcongr
        apply Finset.sum_pos
        · norm_num
          intro aa bb
          exact h aa
        · refine Finset.filter_nonempty_iff.mpr ?_
          exists 0
          norm_num

      -- we have that x_i < 1 + x i < 1 + ∑_{j=0}^i, x j, for every 0 ≤ i ≤ 3
      have lt_sum : ∀ (x : Fin 4 → ℝ) i, (∀ i, 0 < x i) →
        x i < 1 + ∑ j with j ≤ i, x j := by
          intro x i h
          have ltt : x i < 1 + x i := by linarith
          refine lt_of_lt_of_le ltt ?_
          gcongr
          have t_i_eq : x i = ∑ j in {i}, x j := by norm_num
          rw [t_i_eq]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · norm_num
          · norm_num
            intro bb cc dd
            exact le_of_lt (h bb)

      -- every element of f is less than 1
      have f_le_one : ∀ x i, (∀ i, 0 < x i) → f x i < 1 := by
        intro x i h
        unfold f
        rw [div_lt_one]
        · exact lt_sum x i h
        · have pos : 0 ≤ ∑ j ∈ Finset.univ.filter (· ≤ i), x j := by
            apply Finset.sum_nonneg
            norm_num
            intro i ih
            exact le_of_lt (h i)
          positivity

      -- let g_i be `(1 + ∑_{j=0}^i, x j) / (1 + ∑_{j=0}^(i-1), x j)`
      set g := fun (x : Fin 4 → ℝ) i => (1 + ∑ j with j ≤ i, x j) / (1 + ∑ j with j < i, x j)

      -- we have that g is positive
      have g_pos : ∀ (x : Fin 4 → ℝ) i, (∀ i, 0 < x i) → 0 < g x i := by
        intro x i h
        unfold g
        apply div_pos
        have x_pos := h i

        exact x_pos.trans (lt_sum x i h)

        have pos : (0 : ℝ) < 1 + 0 := by linarith
        refine lt_of_lt_of_le pos ?_
        gcongr

        apply Finset.sum_nonneg
        norm_num
        intro i hh
        exact le_of_lt (h i)

      -- Given some 0 < s < 1, (s⁻¹ - 1)⁻¹ + 1 = 1 / (1 - s)
      have s_eq : ∀ {s : ℝ}, 0 < s → s < 1 → (s⁻¹ + (-1))⁻¹ + 1 = 1 / (1 - s) := by
        intro s h1 h2
        ring_nf
        field_simp
        rw [one_add_div]
        · ring
        · linarith

      -- and g_i = (f_i⁻¹ - 1)⁻¹ + 1
      have g_eq : ∀ (x : Fin 4 → ℝ) i, (∀ i, 0 < x i) → g x i = ((f x i)⁻¹ + (-1))⁻¹ + 1 := by
        intro x i h

        rw [s_eq]
        unfold f
        rw [one_sub_div]
        simp only [one_div, inv_div]

        have le_sub_last_eq : ∑ j with j ≤ i, x j - x i = ∑ j with j < i, x j := by
          have i_mem : i ∈ Finset.univ.filter (· ≤ i) := by norm_num
          rw [←Finset.sum_erase_eq_sub i_mem]
          congr
          ext ii
          norm_num
          omega

        rw [add_sub_assoc]
        simp [le_sub_last_eq]

        have sum_pos : 0 ≤ ∑ j with j ≤ i, x j := by
          apply Finset.sum_nonneg
          norm_num
          intro ii hh
          exact le_of_lt (h ii)

        positivity
        exact f_pos x i h
        exact f_le_one x i h

      -- instead of every s which is the maximum of f, we'll consider the every s where 1 / (1 - s) is the maximum of g
      convert_to IsLeast {s | ∃ x, (∀ (i : Fin 4), 0 < x i) ∧ ∑ i : Fin 4, x i = 1 ∧ 0 < s ∧ s < 1 ∧ 1 / (1 - s) = ⨆ i, g x i} _
      · ext s
        refine exists_congr ?_
        simp only [and_congr_right_iff]
        intro x x_pos x_eq

        -- we have 0 < s < 1
        have s_bounds : s = ⨆ i, f x i ↔ 0 < s ∧ s < 1 ∧ s = ⨆ i, f x i := by
          by_cases hh : s = ⨆ i, f x i
          · norm_num [hh]
            have ⟨i, hi⟩ : ∃ i, f x i = ⨆ i, f x i := exists_eq_ciSup_of_finite
            rw [←hi]
            constructor
            · exact f_pos x i x_pos
            · exact f_le_one x i x_pos
          · norm_num [hh]
        rw [s_bounds]

        simp only [and_congr_right_iff]
        intro s_pos s_lt

        -- then we do a bunch of transformations of the supremum
        calc s = ⨆ i, f x i
        -- infinum of inverse
        _ ↔ s⁻¹ = ⨅ i, (f x i)⁻¹ := real_inv_iInf_iff (fun i => f_pos x i x_pos) s
        -- subtract 1
        _ ↔ (s⁻¹ + (-1)) = ⨅ i, ((f x i)⁻¹ + (-1)) := real_add_iInf_iff _ (-1) s⁻¹
        -- supremum of inverse
        _ ↔ (s⁻¹ + (-1))⁻¹ = ⨆ i, ((f x i)⁻¹ + (-1))⁻¹ := by
          have pos : ∀ (i : Fin 4), 0 < (f x i)⁻¹ + -1 := by
            intro i
            norm_num
            exact (one_lt_inv₀ <| f_pos x i x_pos).mpr <| f_le_one x i x_pos
          exact real_inv_iSup_iff pos (s⁻¹ + -1)
        -- add 1
        _ ↔ ((s⁻¹ + (-1))⁻¹ + 1) = ⨆ i, (((f x i)⁻¹ + (-1))⁻¹ + 1) := real_add_iSup_iff _ 1 (s⁻¹ + -1)⁻¹
        -- simplify
        _ ↔ 1 / (1 - s) = ⨆ i, g x i := by
          rw [s_eq s_pos s_lt]
          exact Eq.congr_right <| iSup_congr (Eq.symm <| g_eq x · x_pos)

      -- to show that (1 - 1 / 2 ^ (1 / 4)) is the least value, we'll show that there's x's that achieves it, and that it's a lower bound
      simp only [IsLeast, lowerBounds]

      -- simplify
      simp only [Set.mem_setOf_eq, sub_pos, sub_lt_self_iff, inv_pos, sub_sub_cancel,
        inv_inv, forall_exists_index, and_imp, tsub_le_iff_right]

      constructor
      -- we set
      -- x_0 = 2 ^ (1 / 4) - 1
      -- x_1 = (2 ^ (1 / 4) - 1) * 2 ^ (1 / 4)
      -- x_2 = (2 ^ (1 / 4) - 1) * (2 ^ 2) ^ (1 / 4)
      -- x_3 = (2 ^ (1 / 4) - 1) * (2 ^ 3) ^ (1 / 4)
      · let xs : Fin 4 → ℝ := ![
          2 ^ (1 / 4 : ℝ) - 1,
          (2 ^ (1 / 4 : ℝ) - 1) * 2 ^ (1 / 4 : ℝ),
          (2 ^ (1 / 4 : ℝ) - 1) * (2 ^ 2) ^ (1 / 4 : ℝ),
          (2 ^ (1 / 4 : ℝ) - 1) * (2 ^ 3) ^ (1 / 4 : ℝ)]
        exists xs

        -- 1 < 2 ^ (1 / 4)
        have poss : (1 : ℝ) < 2 ^ (1 / 4 : ℝ) := by
          apply Real.one_lt_rpow
          linarith
          linarith

        -- our x's are valid
        split_ands
        -- they are all positive
        · intro i
          have right_pos : (0 : ℝ) < (2 ^ (1 / 4 : ℝ) - 1) := by linarith

          fin_cases i
          · norm_num [xs]
            exact poss
          all_goals
          · norm_num [xs]
            positivity
        -- they sum to 1
        · norm_num [xs, Fin.sum_univ_four]
          ring_nf
          rw [←Real.mul_rpow]
          rw [←Real.mul_rpow]
          ring_nf
          rw [←Real.rpow_natCast, ←Real.rpow_mul, mul_comm, Real.rpow_mul]
          norm_num

          -- fourth root of 16 is 2
          have sixteen_fourth_root : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
            have sixteen_eq : (16 : ℝ) = 2 ^ (4 : ℝ) := by
              norm_num
            rw [sixteen_eq, ←Real.rpow_mul]
            norm_num
            positivity
          rw [sixteen_fourth_root]
          norm_num
          all_goals positivity
        -- 1 / 2 ^ (1 / 4) < 1
        · rw [one_div_lt, one_div_one]
          exact poss
          positivity
          positivity
        -- 0 < 1 / 2 ^ (1 / 4)
        · positivity
        -- with our chosen xs, g xs is a constant: 2 ^ (1 / 4)
        · have g_const : ∀ i, g xs i = (2 : ℝ) ^ (1 / 4 : ℝ) := by
            intro i
            unfold g xs
            rw [Fin_univ_four]
            fin_cases i
            -- i = 0
            · norm_num
              simp [Finset.filter_insert, Finset.filter_singleton]
            -- i = 1
            · norm_num
              simp [Finset.filter_insert, Finset.filter_singleton]
              ring_nf
              rw [←Real.rpow_natCast, ←Real.rpow_mul, mul_comm _ ((2 : ℕ) : ℝ), Real.rpow_mul,
                ←Real.inv_rpow, ←Real.mul_rpow]
              norm_num
              all_goals positivity
            -- i = 2
            · norm_num
              simp [Finset.filter_insert, Finset.filter_singleton]
              ring_nf
              rw [←Real.inv_rpow, ←Real.mul_rpow, ←Real.rpow_natCast,
                ←Real.rpow_mul, mul_comm _ ((2 : ℕ) : ℝ), Real.rpow_mul,
                ←Real.mul_rpow, ←Real.rpow_natCast, ←Real.rpow_mul,
                mul_comm _ ((2 : ℕ) : ℝ), Real.rpow_mul]
              norm_num
              all_goals positivity
            -- i = 3
            · norm_num
              simp [Finset.filter_insert, Finset.filter_singleton]
              ring_nf
              rw [←Real.mul_rpow, ←Real.rpow_natCast, ←Real.rpow_mul, mul_comm _ ((2 : ℕ) : ℝ), Real.rpow_mul]
              norm_num
              rw [←Real.inv_rpow, ←Real.mul_rpow]
              ring
              all_goals positivity

          norm_num [g_const]
      · intro s x x_pos x_eq s_pos s_lt sup_g

        have s_neg_pos : 0 < 1 - s := by linarith

        -- the product of all g is less than (1 / (1 - s)) ^ 4
        have sup_mul : ∏ j, g x j ≤ ∏ j : Fin 4, 1 / (1 - s) := by
          rw [sup_g]
          exact Fintype_prod_le_prod_iSup_of_nonneg (le_of_lt <| g_pos x · x_pos)

        -- the product of all g elements is 2
        have g_prod : ∏ i, g x i = 2 := by

          -- expand
          rw [Fin.prod_univ_four]
          unfold g
          rw [Fin_univ_four]

          -- we use that ∑ i, x i = 1 to simplify one sum
          have eq_all : ∑ j ∈ Finset.filter (· ≤ 3) {0, 1, 2, 3}, x j = 1 := by
            rw [←x_eq]
            congr

          rw [eq_all]

          -- expand sums, simplify
          simp [Finset.filter_insert, Finset.filter_singleton]
          field_simp

          -- 1 + 1 = 2
          have add_eq : ((1 : ℝ) + 1) = 2 := by linarith only
          rw [add_eq]

          -- cancel factor
          refine mul_div_cancel_left₀ 2 ?_

          -- denominator is not zero, because every term is positive
          -- because every x is positive
          have x_0 := x_pos 0
          have x_1 := x_pos 1
          have x_2 := x_pos 2
          positivity

        -- so we have 2 ≤ ((1 - s) ^ 4)⁻¹
        simp only [g_prod, one_div, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          inv_pow] at sup_mul

        -- which means (1 - s) ^ 4 ≤ 2⁻¹
        rw [←inv_le_inv₀, inv_inv] at sup_mul

        -- take fourth root of both sides
        replace sup_mul := (@Real.rpow_le_rpow_iff _ _ (1 / 4) ?_ ?_ ?_).mpr sup_mul

        -- add s to both sides
        replace sup_mul := (add_le_add_iff_right s).mpr sup_mul

        -- show equality of both sides
        convert sup_mul using 1
        -- simplify powers
        · rw [one_div, ←Real.rpow_natCast, Nat.cast_ofNat, Real.rpow_rpow_inv]
          norm_num
          -- we used that 0 ≤ 1 - s
          exact le_of_lt s_neg_pos
          positivity
        -- simplify powers
        · rw [one_div, ←Real.inv_rpow]
          norm_num
          ring
          positivity

        -- we manipulated positive numbers
        all_goals positivity