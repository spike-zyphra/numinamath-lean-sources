import Mathlib

/- Example 8 Proof: For any integers $x$ and $y$, the algebraic expression $x^{5}+3 x^{4} y-5 x^{3} y^{2}-15 x^{2} y^{3}+4 x y^{4}+12 y^{5}$ cannot equal 33. -/
theorem algebra_270342 (x y : ℤ) :
    x^5 + 3 * x^4 * y - 5 * x^3 * y^2 - 15 * x^2 * y^3 + 4 * x * y^4 + 12 * y^5 ≠ 33
  := by
    -- factor the equation
    have factor : x^5 + 3 * x^4 * y - 5 * x^3 * y^2 - 15 * x^2 * y^3 + 4 * x * y^4 + 12 * y^5
      = (x - 2 * y) * (x - y) * (x + y) * (x + 2 * y) * (x + 3 * y) := by ring

    rw [factor]
    -- consider y = 0
    by_cases h : y = 0
    -- then we want to prove that x ^ 5 ≠ 33
    · rw [h]
      ring_nf

      -- assume that x ^ 5 = 33
      by_contra h

      -- 2 ^ 5 < x ^ 5 < 3 ^ 5
      have low : 2 ^ 5 < x ^ 5 := by
        rw [h]
        norm_num
      have high : x ^ 5 < 3 ^ 5 := by
        rw [h]
        norm_num

      -- x is non-negative
      have x_pos1 : 0 ≤ x ^ 5 := by positivity
      have x_pos2 : 0 ≤ x := by
        refine (Odd.pow_nonneg_iff ?_).mp x_pos1
        decide

      -- 5 is not 0
      have five_ne : 5 ≠ 0 := by omega

      -- so 2 < x < 3
      rw [pow_lt_pow_iff_left₀ zero_le_two x_pos2 five_ne] at low
      rw [pow_lt_pow_iff_left₀ x_pos2 zero_le_three five_ne] at high

      -- but there is not integer strictly between consecutive integers, contradiction
      omega

    -- let f be the products as a tuple
    let f := ![(x - 2 * y), (x - y), (x + y), (x + 2 * y), (x + 3 * y)]

    -- it's a list of five factors
    have f_list : List.ofFn f = [(x - 2 * y), (x - y), (x + y), (x + 2 * y), (x + 3 * y)] := by
      unfold f
      simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, List.ofFn_succ, Fin.isValue,
        Fin.cast_eq_self, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
        List.ofFn_zero]

    -- f is strictly monotone or strictly antitone
    have f_tone : StrictMono f ∨ StrictAnti f := by
      -- y is negative or positive
      rcases lt_trichotomy y 0 with lt | eq | gt
      -- if y is negative, then f is strictly antitone
      · refine Or.inr ?_
        -- we just have to check that the list of factors is sorted, large to small
        have sorted_gt_ofFn_iff {n : ℕ} {f : Fin n → ℤ}
          : List.Sorted (fun (x1 x2 : ℤ) => x1 > x2) (List.ofFn f) ↔ StrictAnti f
            := List.sorted_ofFn_iff
        apply sorted_gt_ofFn_iff.mp

        -- split up into four cases
        rw [f_list]
        simp only [List.sorted_cons_cons, List.sorted_singleton, and_true]

        -- check each case
        omega
      -- y ≠ 0
      · contradiction
      -- if y is positive, then f is strictly monotone
      · refine Or.inl ?_
        -- we just have to check that the list of factors is sorted, small to large
        have sorted_lt_ofFn_iff {n : ℕ} {f : Fin n → ℤ}
          : List.Sorted (fun (x1 x2 : ℤ) => x1 < x2) (List.ofFn f) ↔ StrictMono f
            := List.sorted_ofFn_iff
        apply sorted_lt_ofFn_iff.mp

        -- split up into four cases
        rw [f_list]
        simp only [List.sorted_cons_cons, List.sorted_singleton, and_true]

        -- check each case
        omega

    -- so f is injective
    have f_injective : f.Injective := by
      rcases f_tone with mono | anti
      · exact mono.injective
      · exact anti.injective

    -- so we can write the factors as a product over f
    have as_prod : (x - 2 * y) * (x - y) * (x + y) * (x + 2 * y) * (x + 3 * y)
      = ∏ i : Fin 5, f i := by
        simp only [f, Fin.prod_univ_five, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
    rw [as_prod]


    -- consider f as an embedding (as every factor is distinct)
    let f' : Fin 5 ↪ ℤ := ⟨f, f_injective⟩

    -- let S be the possible factors
    let S := Finset.univ.map f'

    -- there are 5 distinct factors
    have card_S : S.card = 5 := rfl

    have prod_as_map : ∏ i : Fin 5, f i = ∏ i ∈ S, i := by
      simp only [S, Finset.prod_map]
      congr

    rw [prod_as_map]

    -- assume, for contradiction, that the product is equal to 33
    by_contra prod_eq_33

    -- then every element of S will divide 33
    have dvd_33 : ∀ i, i ∈ S → i ∣ 33 := by
      intro i ih
      rw [←prod_eq_33]
      exact Finset.dvd_prod_of_mem id ih

    -- consider all divisors of 33
    let divisors := (Nat.divisors 33).image (fun x : ℕ => (x : ℤ)) ∪ (Nat.divisors 33).image (fun x : ℕ => -(x : ℤ))

    have mem_divisors_of_dvd : ∀ i : ℤ, i ∣ 33 → i ∈ divisors := by
      intro i ih
      unfold divisors
      simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, and_true]
      by_cases hh : 0 ≤ i
      · refine Or.inl ?_
        lift i to ℕ using hh
        exists i
        norm_cast at ih
      · refine Or.inr ?_
        exists i.natAbs
        refine ⟨?_, ?_⟩
        exact Int.ofNat_dvd_right.mp ih
        simp only [Int.natCast_natAbs]
        simp only [not_le] at hh
        rw [abs_of_nonpos (Int.le_of_lt hh)]
        omega

    -- the possible divisors are {±33, ±11, ±3, ±1}
    have divisors_eq : divisors = {33, -33, 11, -11, 3, -3, 1, -1} := by decide

    -- the set of factors is a subset of the divisors
    have S_subs : S ⊆ divisors := by
      intro i ih
      apply mem_divisors_of_dvd
      apply dvd_33
      exact ih

    -- 1 and -1 are the two units of ℤ
    have units_card : ({1, -1} : Finset ℤ).card ≤ 2 := by
        simp only [Int.reduceNeg, Finset.mem_singleton, reduceCtorEq, not_false_eq_true,
          Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd, le_refl]

    -- consider when 33 is one of the factors
    by_cases mem_33 : 33 ∈ S
    -- then we have 33 * ∏ x ∈ (S \ 33), x = 33
    · have not_mem : 33 ∉ S.erase 33 := Finset.not_mem_erase 33 S
      rw [←Finset.insert_erase mem_33, Finset.prod_insert not_mem] at prod_eq_33

      -- then ∏ x ∈ S.erase 33, x = 1
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀] at prod_eq_33

      -- so the product is a unit
      have prod_units : IsUnit (∏ x ∈ S.erase 33, x) := by
        rw [prod_eq_33]
        decide

      -- then every remaining factor is a unit
      rw [IsUnit.prod_iff] at prod_units

      -- which is either 1 or -1
      have rest_sub_units : S.erase 33 ⊆ {1, -1} := by
        intro a ah
        simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton]
        exact Int.isUnit_eq_one_or (prod_units a ah)

      -- but there are 4 remaining factors
      have lhs_card : (S.erase 33).card = 4 := by
        rw [Finset.card_erase_of_mem mem_33, card_S]

      -- so there's not enough possible values, contradiction
      have le_card := Finset.card_le_card rest_sub_units
      omega

    -- so 33 is not one of the factors

    -- similarly, consider when (-33) is one of the factors
    by_cases mem_neg_33 : (-33) ∈ S
    -- then we have -33 * ∏ x ∈ (S \ -33), x = 33
    · have not_mem : (-33) ∉ S.erase (-33) := Finset.not_mem_erase (-33) S
      rw [←Finset.insert_erase mem_neg_33, Finset.prod_insert not_mem] at prod_eq_33

      -- then ∏ x ∈ S.erase (-33), x = -1
      replace prod_eq_33 : ∏ x ∈ S.erase (-33), x = -1 := by
        convert_to 33 * ((-1) * ∏ x ∈ S.erase (-33), x) = 33 at prod_eq_33
        · ring
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          mul_eq_left₀, Int.reduceNeg, neg_mul, one_mul] at prod_eq_33
        exact Int.eq_neg_comm.mp prod_eq_33.symm

      -- so the product is a unit
      have prod_units : IsUnit (∏ x ∈ S.erase (-33), x) := by
        rw [prod_eq_33]
        decide

      -- then every remaining factor is a unit
      rw [IsUnit.prod_iff] at prod_units

      -- which is either 1 or -1
      have rest_sub_units : S.erase (-33) ⊆ {1, -1} := by
        intro a ah
        simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton]
        exact Int.isUnit_eq_one_or (prod_units a ah)

      -- but there are 4 remaining factors
      have lhs_card : (S.erase (-33)).card = 4 := by
        rw [Finset.card_erase_of_mem mem_neg_33, card_S]

      -- so there's not enough possible values, contradiction
      have le_card := Finset.card_le_card rest_sub_units
      omega

    -- so the only possible values are {11, -11, 3, -3, 1, -1}
    replace S_subs : S ⊆ (divisors.erase 33).erase (-33) := by
      simp only [Int.reduceNeg, Finset.subset_erase]
      exact ⟨⟨S_subs, mem_33⟩, mem_neg_33⟩

    convert_to S ⊆ {11, -11, 3, -3, 1, -1} at S_subs
    · decide

    -- assume that 11 is one of the factors
    by_cases mem_11 : 11 ∈ S
    · have not_mem : 11 ∉ S.erase 11 := Finset.not_mem_erase 11 S

      -- then 11 * ∏ x ∈ S \ 11, x = 33
      have split : 11 * ∏ x ∈ S.erase 11, x = 33 := by
        rw [←Finset.insert_erase mem_11, Finset.prod_insert not_mem] at prod_eq_33
        exact prod_eq_33

      -- assume -11 is one of the factors
      by_cases mem_neg_11 : (-11) ∈ S.erase 11
      -- then we have -(121 * ∏ x ∈ (S \ {11, -11}), x) = 33
      · have not_mem_2 : (-11) ∉ (S.erase 11).erase (-11) := Finset.not_mem_erase (-11) (S.erase 11)
        rw [←Finset.insert_erase mem_neg_11, Finset.prod_insert not_mem_2, ←mul_assoc] at split
        norm_num at split

        -- consider sign of ∏ x ∈ (S \ {11, -11}), x
        rcases lt_trichotomy (∏ x ∈ (S.erase 11).erase (-11), x) 0 with h1 | h2 | h3
        -- if it's negative then the equality can't be true
        · linarith
        -- if it's equal to 0, then the equality can't be true
        · rw [h2] at split
          linarith
        -- if it's positive then the equality can't be true
        · linarith

      -- so -11 isn't one of the factors
      replace mem_neg_11 : ¬(-11) ∈ S := by
        simpa only [Int.reduceNeg, Finset.mem_erase, ne_eq, reduceCtorEq, not_false_eq_true,
          true_and] using mem_neg_11


    -- so we can remove -11 from the possible values of S
      replace S_subs : S ⊆ Finset.erase {11, -11, 3, -3, 1, -1} (-11) := by
        rw [Finset.subset_erase]
        exact ⟨S_subs, mem_neg_11⟩

      -- the possible factors are {11, 3, -3, 1, -1}
      convert_to S ⊆ {11, 3, -3, 1, -1} at S_subs

      -- then there are only 5 possible values
      have rest_card : Finset.card {11, 3, -3, 1, -1} = 5 := by decide

      -- so we know all 5 factors, because there are 5 distinct factors
      have eq : S = {11, 3, -3, 1, -1} := by
        apply Finset.eq_of_subset_of_card_le S_subs
        rw [rest_card, card_S]

      -- then the product must be equal to 99
      have prod_eq : ∏ i ∈ S, i = 99 := by
        rw [eq]
        decide

      -- so it's not equal to 33
      omega

    -- so 11 is not part of S
    -- so we can remove 11 from the possible values of S
    replace S_subs : S ⊆ Finset.erase {11, -11, 3, -3, 1, -1} 11 := by
      rw [Finset.subset_erase]
      exact ⟨S_subs, mem_11⟩

    -- the possible values are {-11, 3, -3, 1, -1}
    convert_to S ⊆ {-11, 3, -3, 1, -1} at S_subs

    -- then there are only 5 possible values
    have rest_card : Finset.card {-11, 3, -3, 1, -1} = 5 := by decide

    -- so we know all 5 factors, because there are 5 distinct factors
    have eq : S = {-11, 3, -3, 1, -1} := by
      apply Finset.eq_of_subset_of_card_le S_subs
      rw [rest_card, card_S]

    -- then the product must be equal to -99
    have prod_eq : ∏ i ∈ S, i = -99 := by
      rw [eq]
      decide

    -- so it's not equal to 33
    omega