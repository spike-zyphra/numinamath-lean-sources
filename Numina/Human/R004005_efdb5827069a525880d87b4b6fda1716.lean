import Mathlib

/- If a list contains no zero, it can be split up into positive entries and negative entries.
   Here we express it as a permutation of lists. -/
lemma List_perm_split_lt_of_ne_zero {α : Type*} [LinearOrder α] [Zero α] {l : List α} (h : ¬0 ∈ l)
  : l.Perm (l.filter (0 < ·) ++ l.filter (· < 0)) := by
    -- we split l up into positive and non-positive cases
    have split := l.filter_append_perm (0 < ·)

    -- but non-positive is equal to negative, because l doesn't contain 0
    have not_lt : l.filter (!0 < ·) = l.filter (· < 0) := by
        refine List.filter_congr ?_
        intro aa bb
        refine Bool.not_eq.mpr ?_
        simp only [ne_eq, decide_eq_decide]
        rcases lt_trichotomy 0 aa with h1 | h2 | h3
        · simpa only [h1, true_iff, not_lt] using le_of_lt h1
        · exact absurd (h2 ▸ bb) h
        · simpa only [h3, iff_true, not_lt] using le_of_lt h3

    exact not_lt ▸ split.symm

/- If a list contains no zero, then it contains an odd number of negative numbers iff its product is non-positive. -/
lemma List_odd_neg_iff_prod_nonpos_of_ne_zero  {l : List ℝ} (h : ¬0 ∈ l)
  : Odd (l.filter (· < 0)).length ↔ l.prod ≤ 0 := by
    -- we prove by induction on the list
    induction' l with x xs h3
    -- true for empty lists
    · norm_num
    -- there's no 0 in the tail of the list
    · have ne_zero : ¬0 ∈ xs := by
        norm_num at h
        tauto
      -- we have our induction hypothesis
      replace h3 := h3 ne_zero
      simp only [List.prod_cons]
      -- we match on signs of x
      rcases lt_trichotomy x 0 with lee | eq | gtt
      -- simplify using x < 0
      · norm_num [lee, Nat.odd_add]
        -- use induction hypothesis
        rw [←Nat.not_odd_iff_even, h3, not_le]
        -- match on signs of the product of the tail
        rcases lt_trichotomy xs.prod 0 with h4 | h5 | h6
        · constructor
          all_goals
          · intro aa
            nlinarith
        -- it's not equal to zero
        · rw [List.prod_eq_zero_iff] at h5
          contradiction
        · simp only [h6, true_iff, ge_iff_le]
          exact le_of_lt <| mul_neg_of_neg_of_pos lee h6
      -- x is not 0
      · norm_num [eq] at h
      · norm_num [not_lt_of_gt gtt]
        rw [h3]
        exact le_iff_le_iff_lt_iff_lt.mpr <| (mul_pos_iff_of_pos_left gtt).symm


/- A variant of the AM-GM inequality for lists. -/
lemma List_prod_le_add_div_pow (L : List ℝ) (h : ∀ i ∈ L, 0 ≤ i)
  : L.prod ≤ ((L.sum) / L.length) ^ L.length := by
    -- true for empty lists
    by_cases hL : L.length = 0
    · norm_num [List.length_eq_zero.mp hL]

    -- Every element has the same weight
    have weights_eq : (∑ i : Fin L.length, 1 / (L.length : ℝ)) = 1 := by
      simp only [one_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      refine mul_inv_cancel₀ ?_
      norm_cast

    have prod_nonneg : 0 ≤ L.prod := List.prod_nonneg h
    have sum_nonneg : 0 ≤ L.sum := List.sum_nonneg h

    have am_gm := Real.geom_mean_le_arith_mean Finset.univ (fun i => 1 / (L.length : ℝ)) L.get ?_ ?_ ?_

    rw [weights_eq, div_one, inv_one, Real.rpow_one] at am_gm

    rw [Real.finset_prod_rpow, ←Finset.mul_sum] at am_gm

    have sum_eq : ∑ i : Fin L.length, L.get i = L.sum := by
      rw [←Fin.sum_ofFn, List.ofFn_get]

    have prod_eq : (∏ i : Fin L.length, L.get i) = L.prod := by
      rw [←Fin.prod_ofFn, List.ofFn_get]

    rw [sum_eq, prod_eq] at am_gm
    simp only [one_div_mul_eq_div] at am_gm
    simp only [one_div] at am_gm

    have pow_pos : (0 : ℝ) < L.length := by positivity

    have with_pow := (Real.rpow_le_rpow_iff ?_ ?_ pow_pos).mpr am_gm
    convert with_pow
    · rw [Real.rpow_inv_rpow prod_nonneg]
      norm_cast
    · norm_cast
    positivity
    positivity
    · intro aa bb
      apply h
      exact List.get_mem L aa
    · norm_num
    · norm_num
      refine mul_pos ?_ ?_
      · norm_cast
        positivity
      · norm_num
        positivity
    · intro aa bb
      apply h
      exact List.get_mem L aa

/- A variant of the QM-AM inequality for lists. -/
lemma List_sum_sq {L : List ℝ} (h : ∀ i ∈ L, 0 ≤ i)
  : L.sum ^ 2 / L.length ≤ (L.map (· ^ 2)).sum := by
    -- true for empty lists
    by_cases hL : L.length = 0
    · norm_num [List.length_eq_zero.mp hL]

    -- we use the Cauchy-Schwarz inequality applied to L and ones
    have schwarz := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ L.get 1
    have two_pos : 0 < (2 : ℝ) := by norm_num

    have sum_eq_list_sum : (∑ i : Fin L.length, L.get i ^ 2)
      = (L.map (· ^ 2)).sum := by
        rw [←Fin.sum_ofFn]
        rw [←List.ofFn_get L]
        rw [List.map_ofFn]
        congr 1
        ext i
        norm_num
    rw [sum_eq_list_sum] at schwarz
    norm_num at schwarz
    have squared := (Real.rpow_le_rpow_iff ?_ ?_ two_pos).mpr schwarz

    have len_pos : (0 : ℝ) < L.length := by positivity

    replace squared := (div_le_div_iff_of_pos_right len_pos).mpr squared

    convert squared
    · norm_num
    · have sum_pos : 0 ≤ (List.map (· ^ 2) L).sum := by
        apply List.sum_nonneg
        norm_num [sq_nonneg]
      rw [Real.mul_rpow]
      norm_num
      rw [Real.sq_sqrt sum_pos]
      refine Eq.symm (mul_div_cancel_right₀ _ ?_)
      norm_cast
      · positivity
      · positivity

    · exact List.sum_nonneg h
    · positivity

/- If x is a member of some filtered list, then x has the property that is filtered for. -/
lemma List_mem_filter_prop {A : Type*} {x : A} {L : List A} {p : A → Prop} [DecidablePred p] (h : x ∈ L.filter p)
  : p x := @decide_eq_true_eq (p x) _ ▸ (List.mem_filter.mp h).2

/- If we take the product over a tuple, then negating every element doesn't change
   the result if we have an even number of elements. -/
lemma Fin_prod_even_neg {n : ℕ} (h : Even n) (x : Fin n → ℝ)
: ∏ i : Fin n, (Neg.neg ∘ x) i = ∏ i : Fin n, x i := by
  rw [Finset.prod, ←Multiset.map_map, Multiset.prod_map_neg]
  norm_num [h.neg_one_pow, List.prod_ofFn]

/- Kharkov.

It is known that $x_{1}^{2}+x_{2}^{2}+\ldots+x_{6}^{2}=6$ and $x_{1}+x_{2}+\ldots+x_{6}=0$. Prove that $x_{1} x_{2} \ldots x_{6} \leq 1 / 2$.

# -/
theorem inequalities_229514 (x : Fin 6 → ℝ)
    (h₀ : ∑ i, x i ^ 2 = 6)
    (h₁ : ∑ i, x i = 0) :
    ∏ i, x i ≤ 1 / 2 := by

      -- consider some x is 0
      by_cases hi : 0 ∈ List.ofFn x
      · -- then the product is 0
        have prod_eq_zero : ∏ i : Fin 6, x i = 0 := Fin.prod_ofFn x ▸ List.prod_eq_zero hi
        -- so the bound is true
        norm_num [prod_eq_zero]

      -- so we assume that no x is 0

      -- wlog, there are at most 3 negative x
      wlog hl : ((List.ofFn x).filter (· < 0)).length ≤ 3
      -- else we negative every x
      -- the sum of squares is still 6
      · have sq_sum : ∑ i : Fin 6, (Neg.neg ∘ x) i ^ 2 = 6 := by
          simp only [Function.comp_apply, even_two, Even.neg_pow]
          exact h₀

        -- the sum is still 0
        have sum_eq_zero : ∑ i : Fin 6, (Neg.neg ∘ x) i = 0 := by
          simp only [Function.comp_apply, Finset.sum_neg_distrib, neg_eq_zero]
          exact h₁

        -- -x won't be 0, because x isn't zero
        have ne_zero : ¬0 ∈ List.ofFn (Neg.neg ∘ x) := by
          rwa [←List.map_ofFn, ←neg_zero, List.mem_map_of_injective neg_injective]

        -- at most 3 of x is negative
        have len_le : ((List.ofFn (Neg.neg ∘ x)).filter (· < 0)).length ≤ 3 := by
          -- we have 6 x
          have full_list_len : (List.ofFn x).length = 6 := by norm_num

          -- we just need to count how many of them were positive
          convert_to (List.filter (0 < ·) (List.ofFn x)).length ≤ 3
          · rw [List.ofFn_eq_map, List.ofFn_eq_map, List.comp_map, List.filter_map, List.length_map]
            congr
            ext i
            norm_num

          -- we can split up x into positive and negative
          have split_perm := List_perm_split_lt_of_ne_zero hi

          -- total number of x is equal to positive x plus negative x
          have len_left := List.Perm.length_eq split_perm
          simp only [List.length_append] at len_left

          -- so there are at most 3 positive x
          linarith

        -- then we know that taking the negative of every x means the product is less than 1 / 2
        have app := this (Neg.neg ∘ x) sq_sum sum_eq_zero ne_zero len_le

        -- but if we have 6 elements, then negating every element doesn't change the product
        exact Fin_prod_even_neg (by decide) x ▸ app

      -- consider the case when we have an odd number of negative x
      by_cases odds : Odd ((List.ofFn x).filter (· < 0)).length
      -- we don't have any 0 in the product
      · -- so the product of all x is non-positive
        have prod_non_positive := (List_odd_neg_iff_prod_nonpos_of_ne_zero hi).mp odds
        rw [Fin.prod_ofFn] at prod_non_positive

        -- and 0 < 1 / 2, so we're done
        linarith

      -- let's consider the possible number of negative x
      interval_cases ho : ((List.ofFn x).filter (· < 0)).length
      -- 0 negative x, i.e. every x is positive
      · have x_nonneg : 0 ≤ x := by
          simpa only [List.length_eq_zero, List.filter_eq_nil_iff,
            List.mem_singleton, decide_eq_true_eq, not_lt, List.forall_mem_ofFn_iff] using ho

        -- but x sum to 0, so every x is 0
        have x_eq_zero := (Fintype.sum_eq_zero_iff_of_nonneg x_nonneg).mp h₁

        -- but no x is 0, contradiction
        norm_num [x_eq_zero] at hi

      -- 1 is odd, so already handled
      · norm_num at odds
      -- 2 negative x, let those be x_1 and x_2
      · obtain ⟨x1, x2, hx⟩ := List.length_eq_two.mp ho

        -- they are negative
        have mem_neg : ∀ y, y ∈ (List.ofFn x).filter (· < 0) → y < 0 := fun y => List_mem_filter_prop
        have x1_neg : x1 < 0 := mem_neg x1 (by rw [hx]; norm_num)
        have x2_neg : x2 < 0 := mem_neg x2 (by rw [hx]; norm_num)

        -- we have 6 x in total
        have all_len : (List.ofFn x).length = 6 := rfl

        -- we can split those up into positive and negative x
        have perm_split := List_perm_split_lt_of_ne_zero hi

        -- we have 4 positive
        have pos_eq_four : ((List.ofFn x).filter (0 < ·)).length = 4 := by
          simpa only [hx, all_len, List.length_append, List.length_cons,
            Nat.reduceAdd, Nat.reduceEqDiff, List.length_nil]
              using List.Perm.length_eq perm_split

        -- let those be x_3, x_4, x_5 and x_6
        obtain ⟨x3, x4, x5, x6, hh⟩ : ∃ a b c d, (List.ofFn x).filter (0 < ·) = [a, b, c, d] := by
          -- we have x_3 = a first
          obtain ⟨a, as, hh⟩ := List.exists_of_length_succ _ pos_eq_four
          rw [hh] at pos_eq_four ⊢
          -- and then the rest
          have as_length : as.length = 3 := Nat.succ_inj'.mp pos_eq_four
          obtain ⟨b, c, d, rfl⟩ := List.length_eq_three.mp as_length
          exists a, b, c, d

        -- they are positive
        have mem_pos : ∀ y, y ∈ (List.ofFn x).filter (0 < ·) → 0 < y := fun y => List_mem_filter_prop
        have x3_pos : 0 < x3 := mem_pos x3 (by rw [hh]; norm_num)
        have x4_pos : 0 < x4 := mem_pos x4 (by rw [hh]; norm_num)
        have x5_pos : 0 < x5 := mem_pos x5 (by rw [hh]; norm_num)
        have x6_pos : 0 < x6 := mem_pos x6 (by rw [hh]; norm_num)

        -- the original values of x is a permutation of x_1, x_2, x_3, x_4, x_5 and x_6
        have x_eq : (List.ofFn x).Perm [x1, x2, x3, x4, x5, x6]
          := perm_split.trans <| List.perm_append_comm.trans (hx ▸ hh ▸ List.perm_rfl)

        -- let y_k = |x_k|
        let y : Fin 6 → ℝ := abs ∘ ![x1, x2, x3, x4, x5, x6]

        -- we know the signs of every x_i, so we know the values of y
        have y_0_eq : y 0 = -x1 := abs_of_neg x1_neg
        have y_1_eq : y 1 = -x2 := abs_of_neg x2_neg
        have y_2_eq : y 2 = x3 := abs_of_pos x3_pos
        have y_3_eq : y 3 = x4 := abs_of_pos x4_pos
        have y_4_eq : y 4 = x5 := abs_of_pos x5_pos
        have y_5_eq : y 5 = x6 := abs_of_pos x6_pos

        -- ∑ y_i ^ 2 = 6
        have sum_eq : ∑ i : Fin 6, y i ^ 2 = 6 := by
          rw [Fin.sum_univ_six]
          norm_num [y_0_eq, y_1_eq, y_2_eq, y_3_eq, y_4_eq, y_5_eq]
          rw [←Fin.sum_ofFn] at h₀

          have x_sq_sum : (List.ofFn (x · ^ 2)).sum
            = ([x1, x2, x3, x4, x5, x6].map (· ^ 2)).sum := by
              refine List.Perm.sum_eq ?_
              have fun_eq : (x · ^ 2) = (· ^ 2) ∘ x := rfl
              rw [fun_eq, ←List.map_ofFn]
              exact List.Perm.map _ x_eq
          rw [x_sq_sum] at h₀
          convert h₀
          norm_num
          ring

        -- we have y_0 + y_1 = y_2 + y_3 + y_4 + y_5
        have s_eq : y 0 + y 1 = y 2 + y 3 + y 4 + y 5 := by

          -- rewrite using x_i
          rw [y_0_eq, y_1_eq, y_2_eq, y_3_eq, y_4_eq, y_5_eq]

          -- sum of all x_i is 0
          have sum_eq : x1 + x2 + x3 + x4 + x5 + x6 = 0 := by
            convert h₁
            rw [←Fin.sum_ofFn, List.Perm.sum_eq x_eq]
            norm_num
            ring

          -- so by reordering we see it's true
          linarith

        -- let s be the value of the previous equality
        let s := y 0 + y 1

        -- y_0 and y_1 are non-negative
        have two_pos : ∀ i ∈ [y 0, y 1], 0 ≤ i := by
          norm_num [y, Function.comp_apply, abs_nonneg]

        -- so y_0 * y_1 ≤ (s / 2) ^ 2, according to AM-GM
        have two_le_s : y 0 * y 1 ≤ (s / 2) ^ 2 := by
          have am_gm_two := List_prod_le_add_div_pow [y 0, y 1] two_pos
          norm_num at am_gm_two
          exact am_gm_two

        -- y_2, y_3, y_4 and y_5 are non-negative
        have four_pos : ∀ i ∈ [y 2, y 3, y 4, y 5], 0 ≤ i := by
          norm_num [y, Function.comp_apply, abs_nonneg]

        -- so y_2 * y_3 * y_4 * y_5 ≤ (s / 4) ^ 4 , according to AM-GM
        have four_le_s : y 2 * y 3 * y 4 * y 5 ≤ (s / 4) ^ 4 := by
          have am_gm_four := List_prod_le_add_div_pow [y 2, y 3, y 4, y 5] four_pos
          norm_num at am_gm_four
          convert am_gm_four using 1
          · ring
          · simp_rw [s, s_eq]
            ring

        -- we also have that s ^ / 2 ≤ y_0 ^ 2 + y_1 ^ 2, using QM-AM
        have two_sum_sq : s ^ 2 / 2 ≤ y 0 ^ 2 + y 1 ^ 2 := by
          have sum_sq_two := List_sum_sq two_pos
          norm_num at sum_sq_two
          exact sum_sq_two

        -- we also have that s ^ / 4 ≤ y_2 ^ 2 + y_3 ^ 2 + y_4 ^ 2 + y_5 ^ 2, using QM-AM
        have four_sum_sq : s ^ 2 / 4 ≤ y 2 ^ 2 + y 3 ^ 2 + y 4 ^ 2 + y 5 ^ 2 := by
          have sum_sq_four := List_sum_sq four_pos
          norm_num at sum_sq_four
          convert sum_sq_four using 1
          · congr
            norm_num [s, s_eq]
            ring
          · ring

        -- so then we have that (3 * s ^ 2) / 4 ≤ 6
        have s_le_six : s ^ 2 / 2 + s ^ 2 / 4 ≤ 6 := by
          rw [←sum_eq, Fin.sum_univ_six]
          linarith only [two_sum_sq, four_sum_sq]
        have s_simp : s ^ 2 / 2 + s ^ 2 / 4 = (3 * s ^ 2) / 4 := by ring
        rw [s_simp] at s_le_six


        -- split up the product into positive x and negative x
        rw [←Fin.prod_ofFn, List.Perm.prod_eq perm_split, List.prod_append, hx, hh]

        -- product of negative x is y_0 * y_1
        have left_as_y : [x1, x2].prod = y 0 * y 1 := by
          norm_num [y_0_eq, y_1_eq]

        -- product of positive x is y_2 * y_3 * y_4 * y_5
        have right_as_y : [x3, x4, x5, x6].prod = y 2 * y 3 * y 4 * y 5 := by
          norm_num [y_2_eq, y_3_eq, y_4_eq, y_5_eq]
          ring

        -- so we want to show that (y_0 * y_1) * (y_2 * y_3 * y_4 * y_5) ≤ 1 / 2
        convert_to (y 0 * y 1) * (y 2 * y 3 * y 4 * y 5) ≤ 1 / 2
        · rw [left_as_y, right_as_y]
          ring

        -- but left side is at most (s / 2) ^ 2 * (s / 4) ^ 4
        trans (s / 2) ^ 2 * (s / 4) ^ 4
        · gcongr
          rw [y_2_eq, y_3_eq, y_4_eq, y_5_eq]
          positivity

        -- then we just need to reorder 3 * s ^ 2 / 4 ≤ 6 to show that (s / 2) ^ 2 * (s / 4) ^ 4 ≤ 1 / 2
        field_simp
        rw [←pow_add]
        norm_num
        rw [div_le_iff₀]
        norm_num

        rw [div_le_iff₀, mul_comm, ←le_div_iff₀] at s_le_six
        norm_num at s_le_six

        have cubed := pow_le_pow_left₀ ?_ s_le_six 3
        norm_num [←pow_mul] at cubed
        exact cubed

        -- our operations were valid because everything is positive
        all_goals positivity

      -- 3 is odd, so already handled
      · have three_odd : Odd 3 := by decide
        contradiction