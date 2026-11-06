import Mathlib

/- 2. Using a suitable substitution, determine the number of roots of the equation


$$

8 x\left(1-2 x^{2}\right)\left(8 x^{4}-8 x^{2}+1\right)=1

$$


that lie within the interval $[0,1]$. -/
theorem algebra_208497 (f : ℝ → ℝ) (hf : f = fun x => 8 * x * (1 - 2 * x ^ 2) * (8 * x ^ 4 - 8 * x ^ 2 + 1)) :
    Set.ncard {x | x ∈ Set.Icc 0 1 ∧ f x = 1} = 4 := by
      rw [Set.setOf_and]
      convert_to (Set.Icc 0 1 ∩ {a | f a = 1}).ncard = 4

      -- 0 and 1 are not solutions
      convert_to (Set.Ioo 0 1 ∩ {a | f a = 1}).ncard = 4
      · congr 1
        ext n
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_congr_left_iff]
        intro aa
        constructor
        · intro ha
          rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ha with h0 | h1 | h3
          -- 0 doesn't work
          · rw [hf, h0] at aa
            norm_num at aa
          -- 1 doesn't work
          · rw [hf, h1] at aa
            norm_num at aa
          · exact h3
        · exact Set.mem_Icc_of_Ioo

      -- cos is a bijection from first quarter of circle to [0, 1]
      have quarter_bij : Set.BijOn Real.cos (Set.Icc 0 (Real.pi / 2)) (Set.Icc 0 1) := by
        refine Set.BijOn.mk ?_ ?_ ?_
        · intro a1 a2
          refine ⟨?_, ?_⟩
          apply Real.cos_nonneg_of_mem_Icc
          refine Set.Icc_subset_Icc ?_ (le_refl _) a2
          simp only [Left.neg_nonpos_iff]
          positivity
          exact Real.cos_le_one a1
        · refine Set.InjOn.mono ?_ Real.bijOn_cos.injOn
          refine Set.Icc_subset_Icc (le_refl _) ?_
          refine half_le_self ?_
          exact Real.pi_nonneg

        · simpa only [Real.cos_pi_div_two, Real.cos_zero] using
            intermediate_value_Icc' (le_of_lt Real.pi_div_two_pos) Real.continuous_cos.continuousOn

      -- remove endpoints
      replace quarter_bij : Set.BijOn Real.cos (Set.Ioo 0 (Real.pi / 2)) (Set.Ioo 0 1) := by
        have mem_zero : 0 ∈ Set.Icc 0 (Real.pi / 2)
          := Set.left_mem_Icc.mpr (by positivity)
        have bij_section := quarter_bij.sdiff_singleton mem_zero
        simp only [Set.Icc_diff_left, Real.cos_zero, Set.Icc_diff_right] at bij_section
        have mem_q : (Real.pi / 2) ∈ Set.Ioc 0 (Real.pi / 2)
          := Set.right_mem_Ioc.mpr (by positivity)
        replace bij_section := bij_section.sdiff_singleton mem_q
        simp only [Set.Ioc_diff_right, Real.cos_pi_div_two, Set.Ico_diff_left] at bij_section
        exact bij_section

      -- Consider x = cos t
      rw [quarter_bij.image_eq.symm]
      convert_to ({a | a ∈ Real.cos '' Set.Ioo 0 (Real.pi / 2)} ∩ {a | f a = 1}).ncard = 4
      rw [←Set.setOf_and]
      simp only [Set.mem_image]
      convert_to {a | ∃ x ∈ Set.Ioo 0 (Real.pi / 2), Real.cos x = a ∧ f (Real.cos x) = 1}.ncard = 4
      · congr
        ext n
        simp only [Set.mem_Ioo, Set.mem_setOf_eq]
        constructor
        · intro ⟨⟨x, cc, dd⟩, bb⟩
          refine ⟨x, ?_⟩
          simp only [cc, and_self, dd, bb]
        · intro ⟨x, cc, bb, dd⟩
          rw [bb] at dd
          refine ⟨⟨x, ?_⟩, dd⟩
          simp only [cc, and_self, bb]

      convert_to (Real.cos '' {x | x ∈ Set.Ioo 0 (Real.pi / 2) ∧ f (Real.cos x) = 1}).ncard = 4
      · congr
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_image]
        constructor
        · intro ⟨aa, bb, cc, dd⟩
          refine ⟨aa, ?_⟩
          exact ⟨⟨bb, dd⟩, cc⟩
        · intro ⟨aa, ⟨bb, cc⟩, dd⟩
          refine ⟨aa, ?_⟩
          exact ⟨bb, dd, cc⟩

      -- Applying cos isn't needed for cardinality
      convert_to ({x | x ∈ Set.Ioo 0 (Real.pi / 2) ∧ f (Real.cos x) = 1}).ncard = 4
      · apply Set.ncard_image_of_injOn
        apply Set.InjOn.mono <| Set.sep_subset (Set.Ioo 0 (Real.pi / 2)) fun x => f (Real.cos x) = 1
        exact quarter_bij.injOn

      -- Find solutions of f (cos x) = 1, where x ∈ (0, π / 2)
      have eq_iff : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), f (Real.cos x) = 1
        ↔ (∃ k: ℤ, x = (2 / 9) * k * Real.pi ∨ x = (Real.pi / 7) + (2 / 7) * k * Real.pi) := by
        intro x xh
        simp only [hf]
        calc
          8 * Real.cos x * (1 - 2 * Real.cos x ^ 2) * (8 * Real.cos x ^ 4 - 8 * Real.cos x ^ 2 + 1) = 1
        _ ↔ 8 * Real.cos x * (-(Real.cos (2 * x))) * (Real.cos (4 * x)) = 1 := by
          refine Eq.congr ?_ rfl
          congr 1
          congr
          rw [Real.cos_two_mul]
          simp only [neg_sub]
          refine Eq.symm ?_
          -- four angle formula
          calc Real.cos (4 * x)
          _ = Real.cos (2 * x + 2 * x) := by ring_nf
          _ = Real.cos (2 * x) * Real.cos (2 * x) - Real.sin (2 * x) * Real.sin (2 * x)
            := Real.cos_add (2 * x) (2 * x)
          _ = (Real.cos (x) ^ 2 - Real.sin (x) ^ 2) * (Real.cos (x) ^ 2 - Real.sin (x) ^ 2)
            - (2 * Real.sin x * Real.cos x) * (2 * Real.sin x * Real.cos x) := by {
              rw [Real.cos_two_mul']
              rw [Real.sin_two_mul x]
            }
          _ = Real.cos x ^ 4 - 2 * Real.cos x ^ 2 * Real.sin x ^ 2 + (Real.sin x ^ 2) ^ 2 - 4 * Real.cos x ^ 2 * Real.sin x ^ 2 := by ring_nf
          _ = 8 * Real.cos x ^ 4 - 8 * Real.cos x ^ 2 + 1 := by
            rw [Real.sin_sq]
            ring_nf

        _ ↔ Real.sin x * (8 * Real.cos x * -Real.cos (2 * x) * Real.cos (4 * x)) = Real.sin x := by
          -- Multiple both sides by sin x, which is non-zero when x ∈ (0, π / 2)
          refine ((mul_eq_left₀ ?_)).symm

          -- zero is in the range [-π/2, π/2]
          have zero_mem : 0 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
            simp only [Set.mem_Icc, Left.neg_nonpos_iff, and_self]
            positivity

          -- x is in the range [-π/2, π/2]
          have x_mem : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
            refine Set.Icc_subset_Icc ?_ (le_refl _) <| Set.Ioo_subset_Icc_self xh
            norm_num
            positivity

          -- x is not zero
          have x_ne : 0 ≠ x := by
            by_contra hh
            rw [hh] at xh
            simp only [Set.mem_Ioo, lt_self_iff_false, Nat.ofNat_pos, div_pos_iff_of_pos_right,
              false_and] at xh

          -- But we have that sin is injective on [-π/2, π/2], so the only zero there is x = 0
          have inj := (Real.bijOn_sin.injOn zero_mem x_mem).mt x_ne
          rw [Real.sin_zero] at inj
          exact Ne.symm inj

        _ ↔ -4 * (2 * Real.sin x * Real.cos x) * Real.cos (2 * x) * Real.cos (4 * x) = Real.sin x
          := by ring_nf

        _ ↔ -4 * Real.sin (2 * x) * Real.cos (2 * x) * Real.cos (4 * x) = Real.sin x := by
            rw [Real.two_mul_sin_mul_cos]
            simp only [sub_self, Real.sin_zero, zero_add, ←two_mul]

        _ ↔ -2 * (2 * Real.sin (2 * x) * Real.cos (2 * x)) * Real.cos (4 * x) = Real.sin x
          := by ring_nf

        _ ↔ -(2 * Real.sin (4 * x) * Real.cos (4 * x)) = Real.sin x := by
          rw [Real.two_mul_sin_mul_cos]
          simp only [sub_self, Real.sin_zero, zero_add]
          ring_nf

        _ ↔ Real.sin (x * 8) + Real.sin x = 0 := by
          rw [Real.two_mul_sin_mul_cos]
          simp only [sub_self, Real.sin_zero, zero_add]
          ring_nf
          exact neg_eq_iff_add_eq_zero

        _ ↔ 2 * Real.sin ((9 / 2) * x) * Real.cos ((7 / 2) * x) = 0 := by
          rw [Real.two_mul_sin_mul_cos]
          ring_nf

        _ ↔ (∃ k: ℤ, x = (2 / 9) * k * Real.pi ∨ x = (Real.pi / 7) + (2 / 7) * k * Real.pi) := by
          simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
          constructor
          · intro aa
            cases' aa with aa1 aa2
            · obtain ⟨k, kh⟩ := Real.sin_eq_zero_iff.mp aa1
              refine ⟨k, Or.inl ?_⟩
              linarith only [kh]
            · obtain ⟨k, kh⟩ := Real.cos_eq_zero_iff.mp aa2
              refine ⟨k, Or.inr ?_⟩
              linarith only [kh]
          · intro ⟨k, aa⟩
            cases' aa with aa1 aa2
            · refine Or.inl ?_
              rw [aa1]
              ring_nf
              exact Real.sin_int_mul_pi k
            · refine Or.inr ?_
              rw [aa2]
              convert_to Real.cos ((Real.pi / 2) + k * Real.pi) = 0
              · ring_nf
              rw [Real.cos_add_int_mul_pi]
              simp only [Real.cos_pi_div_two, mul_zero]


      -- Consider the solutions f (cos x) = 1
      convert_to ({x | x ∈ Set.Ioo 0 (Real.pi / 2)
          ∧ ∃ k : ℤ, x = 2 / 9 * k * Real.pi ∨ x = Real.pi / 7 + 2 / 7 * k * Real.pi}).ncard = 4
      · congr
        ext a
        simp only [Set.mem_image, Set.mem_setOf_eq]
        constructor
        · intro ⟨aa, bb⟩
          refine ⟨aa, ?_⟩
          exact (eq_iff a aa).mp bb
        · intro ⟨aa, bb⟩
          refine ⟨aa, ?_⟩
          exact (eq_iff a aa).mpr bb

      -- We see there's only four possible values
      convert_to Finset.card {(2 / 9) * Real.pi, (4 / 9) * Real.pi, (Real.pi / 7), (Real.pi / 7) + 2 / 7 * 1 * Real.pi} = 4
      · rw [←Set.ncard_coe_Finset]
        congr
        ext x
        simp only [Set.mem_setOf_eq, mul_one, Finset.coe_insert,
          Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro ⟨aa, k, kh⟩
          -- x has two possible forms
          cases' kh with h1 h2
          · rw [h1] at aa
            simp only [Set.mem_Ioo] at aa
            have ⟨aa1, aa2⟩ := aa

            -- lower bound on k
            have : 0 < k := by
              ring_nf at aa1
              field_simp at aa1
              exact aa1

            -- upper bound on k
            have upper_bound' : (2 / 9 * ↑k * Real.pi) * (1 / Real.pi) < (Real.pi / 2) * (1 / Real.pi) := by
              refine (mul_lt_mul_iff_of_pos_right ?_).mpr aa2
              positivity
            ring_nf at upper_bound'
            field_simp at upper_bound'

            have : k ≤ 3 := by
              have k_le : (k : ℝ) ≤ 3 := by linarith only [upper_bound']
              convert_to (k : ℝ) ≤ ((3 : ℤ) : ℝ) at k_le
              exact Int.cast_le.mp k_le

            interval_cases k
            -- 1 is valid
            · refine Or.inl ?_
              rw [Int.cast_one, mul_one] at h1
              exact h1
            -- 2 is valid
            · rw [Int.cast_ofNat] at h1
              refine Or.inr <| Or.inl ?_
              convert h1 using 2
              norm_num
            -- 3 is invalid
            · norm_num at upper_bound'
          · rw [h2] at aa
            simp only [Set.mem_Ioo] at aa
            have ⟨aa1, aa2⟩ := aa

            -- lower bound on k
            ring_nf at aa1
            field_simp at aa1
            have k_le : (-Real.pi) * (1 / (Real.pi * 2)) < (Real.pi * k * 2) * (1 / (Real.pi * 2))
              := (mul_lt_mul_iff_of_pos_right (by positivity)).mpr (by linarith)


            ring_nf at k_le
            field_simp at k_le
            have k_le' : (-1 : ℝ) ≤ k := by linarith only [k_le]
            convert_to ((-1 : ℤ) : ℝ) ≤ k at k_le'
            · rw [Int.cast_neg, Int.cast_one]
            rw [Int.cast_le] at k_le'

            -- upper bound on k
            have k_up : Real.pi / 7 + 2 / 7 * ↑k * Real.pi - Real.pi / 7 < Real.pi / 2 - Real.pi / 7
              := sub_lt_sub_right aa2 (Real.pi / 7)

            replace k_up : (Real.pi / 7 + 2 / 7 * k * Real.pi - Real.pi / 7) * (1 / (2 / 7 * Real.pi))
              < (Real.pi / 2 - Real.pi / 7)  * (1 / (2 / 7 * Real.pi)) := by
              refine (mul_lt_mul_iff_of_pos_right ?_).mpr k_up
              positivity

            ring_nf at k_up
            field_simp at k_up
            have k_up' : (k : ℝ) ≤ 2 := by linarith only [k_up]
            convert_to (k : ℝ) ≤ ((2 : ℤ) : ℝ) at k_up'
            rw [Int.cast_le] at k_up'
            interval_cases k
            -- -1 is invalid
            · norm_num at k_le
            -- 0 is valid
            · simp only [Int.cast_zero, mul_zero, zero_mul, add_zero] at h2
              exact Or.inr <| Or.inr <| Or.inl h2
            -- 1 is valid
            · simp only [Int.cast_one, mul_one] at h2
              exact Or.inr <| Or.inr <| Or.inr h2
            -- 2 is invalid
            · norm_num at k_up
        -- The four values we provided are valid
        · intro h
          rcases h with a1 | a2 | a3 | a4
          · rw [a1]
            refine ⟨?_, 1, ?_⟩
            · simp only [Set.mem_Ioo, Nat.ofNat_pos, div_pos_iff_of_pos_left,
                mul_pos_iff_of_pos_left]
              refine ⟨?_, ?_⟩
              · positivity
              · apply lt_add_neg_iff_lt.mp
                ring_nf
                positivity
            · simp only [Int.cast_one, mul_one, true_or]
          · rw [a2]
            refine ⟨?_, 2, ?_⟩
            · simp only [Set.mem_Ioo, Nat.ofNat_pos, div_pos_iff_of_pos_left,
                mul_pos_iff_of_pos_left]
              refine ⟨?_, ?_⟩
              · positivity
              · apply lt_add_neg_iff_lt.mp
                ring_nf
                positivity
            · simp only [Int.cast_ofNat, mul_eq_mul_right_iff]
              refine Or.inl <| Or.inl ?_
              norm_num
          · rw [a3]
            refine ⟨?_, 0, ?_⟩
            · simp only [Set.mem_Ioo, Nat.ofNat_pos, div_pos_iff_of_pos_right]
              refine ⟨?_, ?_⟩
              · positivity
              · apply lt_add_neg_iff_lt.mp
                ring_nf
                positivity
            · simp only [Int.cast_zero, mul_zero, zero_mul, div_eq_zero_iff, OfNat.ofNat_ne_zero,
              or_false, add_zero, or_true]
          · rw [a4]
            refine ⟨?_, 1, ?_⟩
            · simp only [Set.mem_Ioo]
              refine ⟨?_, ?_⟩
              · positivity
              · apply lt_add_neg_iff_lt.mp
                ring_nf
                positivity
            · simp only [Int.cast_one, mul_one, or_true]

      -- and the values are all different, so there are 4 possible roots
      iterate 3 rw [Finset.card_insert_eq_ite]
      ring_nf
      simp only [one_div, Finset.mem_insert, mul_eq_mul_left_iff, Real.pi_ne_zero, or_false,
        Finset.mem_singleton, Finset.card_singleton, Nat.reduceAdd]
      norm_num