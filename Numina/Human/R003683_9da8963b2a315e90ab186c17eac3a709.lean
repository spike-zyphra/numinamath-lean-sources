import Mathlib

/- For a set S, the "S different from x" operation is bijective on subsets of S. -/
lemma diff_bijon_powerset {A : Type*} [DecidableEq A] (S : Finset A)
  : Set.BijOn (S \ ·) S.powerset S.powerset := by
    -- It maps from subsets of S to subsets of S
    have maps : Set.MapsTo (S \ ·) S.powerset S.powerset := by
      intro a b
      simp only [Finset.coe_powerset, Set.mem_preimage, Finset.coe_sdiff, Set.mem_powerset_iff]
      exact Set.diff_subset

    -- it's injective on subsets of S
    have inj : Set.InjOn (S \ ·) S.powerset := by
      intro a ha b hb eq
      simp only at eq
      have a_sub : a ⊆ S := Finset.mem_powerset.mp ha
      have b_sub : b ⊆ S := Finset.mem_powerset.mp hb
      exact eq_of_sdiff_eq_sdiff a_sub b_sub eq

    -- it's surjective on subsets of S
    have surj : Set.SurjOn (S \ ·) S.powerset S.powerset := by
      intro a ha
      simp only [Finset.coe_powerset, Set.mem_image, Set.mem_preimage, Set.mem_powerset_iff,
        Finset.coe_subset]
      exists S \ a
      split_ands
      · exact Finset.sdiff_subset
      · simp only [sdiff_sdiff_right_self, Finset.inf_eq_inter, Finset.inter_eq_right]
        exact Finset.mem_powerset.mp ha

    -- so it's bijective on subsets of S
    exact Set.BijOn.mk maps inj surj

/- A sum over subsets of S, is the same as a sum over S different from subsets of S. -/
lemma powerset_sum_diff {A : Type*} [DecidableEq A] (S : Finset A) (f : Finset A → ℝ)
  : ∑ T ∈ S.powerset, f T = ∑ T ∈ S.powerset, f (S \ T) := by
    have bijon := diff_bijon_powerset S
    refine Finset.sum_bij ?_ ?_ ?_ ?_ ?_
    · intro T hT
      exact S \ T
    · exact bijon.mapsTo
    · exact bijon.injOn
    · intro T hT
      exact bex_def.mpr (bijon.surjOn hT)
    · norm_num
      intro T hT
      congr
      exact ((Finset.inter_eq_right.mpr) hT).symm

/- x + (1 / x) is at least 2, when x is positive. -/
lemma Real_two_le_add_inv_of_pos (x : ℝ) (h : 0 < x) : 2 ≤ x + (1 / x) := by

  -- multiply both sides by x
  suffices : 2 * x ≤ (x + 1 / x) * x
  · nlinarith

  -- multiplication distributes
  have mul_distrib : (x + 1 / x) * x = x ^ 2 + 1 := by
    field_simp
    ring
  rw [mul_distrib]

  -- move terms to RHS
  suffices : 0 ≤ x ^ 2 - 2 * x + 1
  · nlinarith

  -- offset the graph to the right
  obtain ⟨x', xh⟩ : ∃ x', x = x' + 1 := by
    exists x - 1
    linarith

  subst xh
  ring_nf

  -- clearly x' ^ 2 is positive
  positivity


/- ![](https://cdn.mathpix.com/cropped/2024_05_06_88363d92b48074f4f115g-21.jpg?height=108&width=1187&top_left_y=1604&top_left_x=1)

Prove the inequality $\left(1+x_{1}\right) \ldots\left(1+x_{n}\right) \geq 2^{n}$, where $x_{1} \ldots x_{n}=1$.

The values of the variables are considered positive. -/
theorem inequalities_207337 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
  (hx : ∀ i, 0 < x i) (hxp : ∏ i, x i = 1) :
  ∏ i, (1 + x i) ≥ 2 ^ n := by
    -- use ≤ instead of ≥
    simp only [ge_iff_le]

    -- we have ∏ i ∈ [0, n), (1 + x i) = ∑ T ∈ 2 ^ [0, n), ∏ i ∈ T, x i
    rw [Finset.prod_one_add]

    -- we have a positive number of variables
    have nonempty_variables : (Finset.univ : Finset (Fin n)).Nonempty := by
      simpa only [←Finset.card_pos, Finset.card_univ, Fintype.card_fin] using hn

    -- let a be the index one of the variables
    obtain ⟨a, ah⟩ := nonempty_variables

    -- then we can seperate a from the other variables
    have erased : (Finset.univ : Finset (Fin n))
      = insert a ((Finset.univ : Finset (Fin n)).erase a)
        := (Finset.insert_erase ah).symm

    rw [erased]

    set S := (Finset.univ.erase a)

    -- a is not one of the other variables
    have not_mem : ¬a ∈ S := Finset.not_mem_erase a Finset.univ

    -- split up the powerset sum into sets with a and sets without a
    rw [Finset.sum_powerset_insert not_mem]

    -- we have ∑ T ∈ 2 ^ [0, n), ∏ i ∈ a + T, x i
    -- = ∑ T ∈ 2 ^ [0, n), ∏ i ∈ a + (S \ T), x i
    rw [powerset_sum_diff S (∏ i ∈ insert a ·, x i)]

    -- the addition of a commutes with set difference in the sum
    have sum_eq : ∑ T ∈ S.powerset, ∏ i ∈ insert a (S \ T), x i
      = ∑ T ∈ S.powerset, ∏ i ∈ ((insert a S) \ T), x i := by
        apply Finset.sum_congr rfl
        intro T hT

        have insert_eq : insert a (S \ T) = (insert a S) \ T := by
          refine (Finset.insert_sdiff_of_not_mem S ?_).symm
          exact Finset.not_mem_of_mem_powerset_of_not_mem hT not_mem

        rw [insert_eq]

    rw [sum_eq]

    -- Use that product of the variables equal 1 to express sum as sum over inverse
    have sum_eq_2 : ∑ T ∈ S.powerset, ∏ i ∈ insert a S \ T, x i
      = ∑ T ∈ S.powerset, (1 / ∏ i ∈ T, x i) := by
        apply Finset.sum_congr rfl
        intro T hT

        -- the product equals 1
        have prod_eq_one : ∏ i ∈ insert a S, x i = 1 := by
          rw [←erased]
          exact hxp

        have sdiff_subs : T ⊆ insert a S := by
          trans S
          exact Finset.mem_powerset.mp hT
          exact Finset.subset_insert a S

        -- any product over T does not equal 0
        have prod_eq : ∏ i ∈ T, x i ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          intro i hi
          exact (ne_of_lt (hx i)).symm

        field_simp

        -- Any product over a set can be split up into two parts
        have factored := @Finset.prod_sdiff (Fin n) ℝ T (insert a S) x _ _ sdiff_subs
        rw [prod_eq_one] at factored

        exact factored

    rw [sum_eq_2]

    -- combine the two sums over subsets of S
    rw [←Finset.sum_add_distrib]

    -- The sum of subsets of S, where each term equals two, is 2 ^ n
    have pow_eq_powerset_sum : (2 : ℝ) ^ n = ∑ T ∈ S.powerset, 2 := by
      norm_num
      have all_card : (insert a S).card = n := by
        rw [←erased]
        norm_num
      have S_card : S.card = n - 1 := by
        simp only [not_mem, not_false_eq_true, Finset.card_insert_of_not_mem] at all_card
        omega
      rw [S_card]
      refine (pow_sub_one_mul ?_ 2).symm
      exact Nat.not_eq_zero_of_lt hn

    rw [pow_eq_powerset_sum]

    -- each RHS terms is larger than 2
    apply Finset.sum_le_sum
    intro T hT

    -- x + (1 / x) is larger than 2 if x is positive
    apply Real_two_le_add_inv_of_pos

    -- and each product of subset of variables is positive, because each variable is positive
    apply Finset.prod_pos

    intro a ha
    exact hx a