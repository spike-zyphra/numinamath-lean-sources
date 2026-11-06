import Mathlib

/-
3. There are numbers 1,2,.., 33 written on a blackboard. In one step we choose two numbers on the blackboard such that one of them divides the other one, we erase the two numbers and write their integer quotient instead. We proceed in this manner until no number on the blackboard divides another one. What is the least possible amount of numbers left on the blackboard?
 -/
theorem number_theory_289828 :
    IsLeast ((fun ⟨k, S⟩ => (S (Fin.last k)).card )
      '' {⟨k, S⟩ : (k : ℕ) × (Fin (k + 1) → Multiset ℕ)
      | S 0 = Multiset.Icc 1 33
      ∧ (∀ i : Fin k, ∃ a b,
          {a, b} ≤ S i.castSucc
          ∧ a ∣ b
          ∧ S i.succ = S i.castSucc - {a, b} + {b / a})}
    ) 7 := by
      split_ands
      -- First we show that it's possible to reach just 7 numbers
      · simp only [Set.mem_image, Set.mem_setOf_eq, Sigma.exists]
        -- We have an explicit list of pairs on the blackboard which we pick each step.
        let f : List (ℕ × ℕ) :=
          [(32, 16), (30, 15), (28, 14), (26, 13), (24, 12), (22, 11),
           (27, 9), (21, 7), (18, 6), (25, 5), (20, 4), (8, 2), (5, 5),
           (4, 2), (3, 3), (3, 3), (2, 2), (2, 2), (2, 2), (17, 1),
           (17, 1), (17, 1), (17, 1), (17, 1), (17, 1), (17, 1)]

        -- then we consider all numbers on the blackboard after every step
        let g : List (Multiset ℕ) := List.scanl (fun S ⟨b, a⟩ => S - {a, b} + {b / a}) (Multiset.Icc 1 33) f

        exists 26, g.get
        · split_ands
          -- we start with the numbers 1, 2, .., 33
          · rfl
          -- each step is valid
          · intro i
            exists (f.get i).2, (f.get i).1
            fin_cases i <;> decide
          -- we end up with just 7 numbers in the end
          · decide

      -- then we show that 7 is a lower bound
      · simp only [mem_lowerBounds, Set.mem_image, Set.mem_setOf_eq, Sigma.exists, forall_exists_index, and_imp]
        rintro card k S S_0 hh rfl

        -- The numbers on the blackboard is always contained in [1, 33]
        have S_sub (i : Fin (k + 1)) : S i ⊆ Multiset.Icc 1 33 := by
          -- we prove by induction
          induction' i using Fin.induction with i hi
          -- the starting blackboard contains [1, 33]
          · simpa only [S_0] using Multiset.Subset.refl _
          · obtain ⟨a, b, h1, h2, h3⟩ := hh i
            rw [h3]

            -- we prove it separately for the newly added number and the rest
            suffices : S i.castSucc - {a, b} ⊆ Multiset.Icc 1 33 ∧ {b / a} ⊆ Multiset.Icc 1 33
            · simp only [←Multiset.toFinset_subset, Multiset.toFinset_add] at this ⊢
              exact Finset.union_subset this.1 this.2

            split_ands
            -- the rest are contained in [1, 33] by induction
            · have sub_le_self := Multiset.sub_le_self (S i.castSucc) {a, b}
              exact Multiset.Subset.trans (Multiset.subset_of_le sub_le_self) hi

            -- we have a, b ∈ [1, 33] so b / a ∈ [1, 33] too
            · have a_b_subs : {a, b} ⊆ Multiset.Icc 1 33
                := Multiset.Subset.trans (Multiset.subset_of_le h1) hi
              simp at a_b_subs ⊢
              split_ands
              -- lower bound
              · exact Nat.div_pos (Nat.le_of_dvd (by omega) h2) (by omega)
              -- upper bound
              · exact (Nat.div_le_self b a).trans (by omega)

        -- If n ∈ [2, 23], and for every i ≠ n where i and n does not divide each other
        -- then there's always exactly one n on the blackboard
        have remains (n : ℕ) (h1 : n ∈ Multiset.Icc 2 33)
          (h2 : ∀ i ∈ Multiset.Icc 2 33, i ≠ n → ¬(i ∣ n) ∧ ¬(n ∣ i))
          : ∀ j, (S j).count n = 1 := by
            intro j
          -- we prove by induction
            induction' j using Fin.induction with j hj
            -- the starting board has all numbers in [1, 33] with
            -- no duplicates, so there's one 1 there
            · norm_num [S_0, Multiset.count_eq_of_nodup Multiset.nodup_Icc] at h1 ⊢
              omega
            · obtain ⟨a, b, h3, h4, h5⟩ := hh j
              rw [h5]
              simp only [Multiset.count_add, Multiset.count_singleton, Multiset.count_sub, hj]

              -- not that n ≠ 1
              norm_num at h1
              have n_ne_one : ¬n = 1 := by omega


              -- consider when a = 1
              by_cases a_eq_one : a = 1
              · subst a_eq_one

                -- then if b = n we removed and added one n, else we didn't add or remove any n
                simp [Multiset.count_cons, n_ne_one, Multiset.count_singleton]
                by_cases n_eq_b : n = b <;> norm_num [n_eq_b]

              -- consider when b = 1
              by_cases b_eq_one : b = 1
              · -- then a is 1 too, which we already handled
                simp only [b_eq_one, Nat.dvd_one] at h4
                exact absurd rfl (h4 ▸ a_eq_one)

              -- we have a, b ∈ [1, 33]
              have a_b_sub : {a, b} ⊆ Multiset.Icc 1 33
                := Multiset.Subset.trans (Multiset.subset_of_le h3) (S_sub j.castSucc)

              -- furthermore, we have a, b ∈ [2, 33]
              replace a_b_sub : {a, b} ⊆ Multiset.Icc 2 33 := by
                convert_to {a, b} ⊆ (Multiset.Icc 1 33).erase 1
                simp only [Multiset.insert_eq_cons, Multiset.cons_subset,
                  Multiset.singleton_subset] at a_b_sub ⊢
                split_ands
                · simpa only [Multiset.mem_erase_of_ne a_eq_one] using a_b_sub.1
                · simpa only [Multiset.mem_erase_of_ne b_eq_one] using a_b_sub.2

              have a_mem : a ∈ Multiset.Icc 2 33 := a_b_sub (by norm_num)
              have b_mem : b ∈ Multiset.Icc 2 33 := a_b_sub (by norm_num)

              -- at most one of a and b are n
              have count_ab : Multiset.count n ({a, b}) ≤ 1
                := hj ▸ Multiset.count_le_of_le n h3

              -- so consider cases
              by_cases a_eq : a = n
              · by_cases b_eq : b = n
                -- a being n is impossible
                · norm_num [a_eq, b_eq] at count_ab
                -- a = n and b ≠ n is impossible because then n divides b
                · have ⟨_, dvd_2⟩ := h2 b b_mem b_eq
                  exact absurd (a_eq ▸ h4) dvd_2
              · by_cases b_eq : b = n
                -- a ≠ n and b = n is impossible because then a divides n
                · have ⟨dvd_1, _⟩ := h2 a a_mem a_eq
                  exact absurd (b_eq ▸ h4) dvd_1
                -- so consider when a, b ≠ n
                -- then we didn't remove any n from the blackboard
                · have count_none : Multiset.count n {a, b} = 0 := by
                    norm_num
                    tauto
                  rw [count_none]

                  -- then we just need to show that we didn't add any n
                  -- i.e. n ≠ b / a
                  norm_num

                  -- note that a is positive
                  have a_pos : 0 < a := by
                    · norm_num at a_mem
                      omega

                  -- then we just need to show that n doesn't divide b
                  suffices : ¬(n ∣ b)
                  · obtain ⟨k, kh⟩ : ∃ k, b = a * k := h4
                    have k_ne : k ≠ 0 := by
                      by_contra hh
                      norm_num [kh, hh] at b_mem
                    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := Nat.exists_eq_succ_of_ne_zero k_ne
                    rw [kh]
                    ring_nf
                    rw [Nat.add_div a_pos, Nat.mul_div_cancel_left k a_pos, Nat.div_self a_pos]
                    have ne_zero : ¬a = 0 := by omega
                    simp [ne_zero]
                    by_contra n_eq
                    rw [n_eq, kh, add_comm 1] at this
                    have dvd : k + 1 ∣ a * (k + 1) := Nat.dvd_mul_left (k + 1) a
                    contradiction

                  -- and we already know that n doesn't divide b
                  exact (h2 b b_mem b_eq).2

        -- so there is always one of 17, 19, 23, 29 and 31 on the blackboard
        have ⟨count_17, count_19, count_23, count_29, count_31⟩
          : (∀ j, (S j).count 17 = 1)
          ∧ (∀ j, (S j).count 19 = 1)
          ∧ (∀ j, (S j).count 23 = 1)
          ∧ (∀ j, (S j).count 29 = 1)
          ∧ (∀ j, (S j).count 31 = 1) := by
            split_ands
            all_goals
            · apply remains
              · decide
              · simp only [Multiset.mem_Icc, ne_eq, and_imp]
                intro i hi ih ne
                rcases lt_or_gt_of_ne ne with hh | hh <;> interval_cases i <;> decide

        -- so 17, 19, 23, 29 and 31 are on the blackbaord in the end
        have subs : {17, 19, 23, 29, 31} ⊆ S (Fin.last _) := by
          simp
          split_ands
          all_goals
          · exact Multiset.count_pos.mp <| Nat.lt_of_sub_eq_succ <| by tauto
        have lee : {17, 19, 23, 29, 31} ≤ S (Fin.last _) := (Multiset.le_iff_subset (by decide)).mpr subs

        -- now let S be the product of all numbers on the blackboard

        -- then if the multiplicity of some prime p in S is odd at some timestep i, then it's also odd at i + 1
        have multi (i : Fin k) (p : ℕ) (hp : Prime p) (hi : Odd (multiplicity p (S i.castSucc).prod)) : Odd (multiplicity p (S i.succ).prod) := by
          -- at this step, we removed a and b, where a divides b, from the blackboard and wrote b / a
          obtain ⟨a, b, h1, h2, h3⟩ := hh i

          -- a is positive
          have a_pos : 0 < a := by
            have a_b_subs : {a, b} ⊆ Multiset.Icc 1 33
                := Multiset.Subset.trans (Multiset.subset_of_le h1) (S_sub _)
            norm_num at a_b_subs
            omega

          -- then the product of all the numbers on the blackboard will change by removing a factor of a ^ 2
          have prod_eq : (S i.castSucc).prod = (S i.succ).prod * a ^ 2 := by
            rw [h3]
            simp only [Multiset.prod_add, Multiset.prod_singleton]
            obtain ⟨R, hR⟩ : ∃ R, S i.castSucc = {a, b}  + R
              := Multiset.le_iff_exists_add.mp h1
            rw [hR]
            simp
            convert_to a * (b * R.prod) = R.prod * (a * (b / a)) * a
            · ring
            rw [Nat.mul_div_cancel' h2]
            ring

          -- so the multiplicity will still be odd
          rw [prod_eq, multiplicity_mul hp, FiniteMultiplicity.multiplicity_pow hp] at hi
          have add_even : Even (2 * multiplicity p a) := even_two_mul (multiplicity p a)
          simp only [Nat.odd_add, add_even, iff_true] at hi
          exact hi

          -- we implicitly used that our values have finite multiplicity
          · rw [Nat.finiteMultiplicity_iff]
            exact ⟨hp.ne_one, a_pos⟩
          · rw [Nat.finiteMultiplicity_iff]
            refine ⟨hp.ne_one, ?_⟩
            simp
            split_ands
            · intro x xh
              have hmm := S_sub i.succ
              have x_mem : x ∈ Multiset.Icc 1 33 := S_sub i.succ xh
              norm_num at x_mem
              omega
            · positivity

        -- so if the multiplicity of some prime p in S is odd in the beginning, then it's multiplicity will always be positive
        replace multi (i : Fin (k + 1)) (p : ℕ) (hp : Nat.Prime p) (hi : Odd (multiplicity p (S 0).prod)) : 0 < multiplicity p (S i).prod := by
          refine Odd.pos ?_
          induction' i using Fin.induction with i hi
          · exact hi
          · exact multi i p hp.prime hi

        -- specifically for the final numbers on the blackboard
        specialize multi (Fin.last _)

        -- note that if x ∈ [1, 33], then x ≠ 0
        have ne_zero : ∀ x ∈ Finset.Icc 1 33, x ≠ 0 := by
          norm_num
          omega

        -- calculate multiplicity of 2, 3, 5, 11 at the start (which are all odd)
        have ⟨mul_2, mul_3, mul_5, mul_11⟩
          : multiplicity 2  (∏ i ∈ (Finset.Icc 1 33), i) = 31
          ∧ multiplicity 3  (∏ i ∈ (Finset.Icc 1 33), i) = 15
          ∧ multiplicity 5  (∏ i ∈ (Finset.Icc 1 33), i) = 7
          ∧ multiplicity 11 (∏ i ∈ (Finset.Icc 1 33), i) = 3
          := by
            split_ands
            all_goals
            · rw [Nat.multiplicity_eq_factorization (by decide) (Finset.prod_ne_zero_iff.mpr ne_zero),
                Nat.factorization_prod ne_zero]
              simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Nat.reduceAdd, Nat.one_le_ofNat,
                Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton, Nat.factorization_one,
                Finsupp.coe_zero, Pi.zero_apply, zero_add]
              norm_num [←Nat.primeFactorsList_count_eq, Nat.primeFactorsList]

        -- the product of all numbers at the start is just ∏ i ∈ [1, 33], i
        have prod_zero : (S 0).prod = (∏ i ∈ Finset.Icc 1 33, i) := by congr
        rw [prod_zero] at multi

        -- so the multiplicity of 2, 3, 5 and 11 are all positive in the end
        replace ⟨mul_2, mul_3, mul_5, mul_11⟩
          : 0 < emultiplicity 2  (S (Fin.last _)).prod
          ∧ 0 < emultiplicity 3  (S (Fin.last _)).prod
          ∧ 0 < emultiplicity 5  (S (Fin.last _)).prod
          ∧ 0 < emultiplicity 11 (S (Fin.last _)).prod
          := by
            split_ands
            all_goals
            · refine emultiplicity_pos_iff.mpr ?_
              apply multi
              · decide
              · simp only [mul_2, mul_3, mul_5, mul_11]
                decide

        -- We know that 17, 19, 23, 29 and 31 are on the blackboard in the end
        -- so let R be the remaining numbers
        obtain ⟨R, hR⟩ : ∃ R, S (Fin.last k) = {17, 19, 23, 29, 31} + R
          := Multiset.le_iff_exists_add.mp lee

        -- then we just need to show that R consists of at least 2 numbers
        suffices : 2 ≤ R.card
        · norm_num [hR]
          omega

        -- and 2, 3, 5, 11 doesn't divide any of 17, 19, 23, 29 or 31
        -- so they must divide the product of all numbers in R
        replace ⟨mul_2, mul_3, mul_5, mul_11⟩
          : 0 < multiplicity 2  R.prod
          ∧ 0 < multiplicity 3  R.prod
          ∧ 0 < multiplicity 5  R.prod
          ∧ 0 < multiplicity 11 R.prod
          := by
            simp only [hR, Multiset.prod_add] at mul_2 mul_3 mul_5 mul_11
            rw [emultiplicity_mul (by norm_num [←Nat.prime_iff])] at mul_2 mul_3 mul_5 mul_11
            simp only [Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton,
              Nat.reduceMul, add_pos_iff] at mul_2 mul_3 mul_5 mul_11
            rw [emultiplicity_pos_iff,emultiplicity_pos_iff,
              Nat.multiplicity_eq_factorization (by decide) (by decide)] at mul_2 mul_3 mul_5 mul_11
            norm_num [←Nat.primeFactorsList_count_eq, Nat.primeFactorsList] at mul_2 mul_3 mul_5 mul_11
            exact ⟨mul_2, mul_3, mul_5, mul_11⟩

        -- so assume R doesn't contain at least 2 numbers
        by_contra R_one
        interval_cases card_eq : R.card
        -- consider when it's empty
        · norm_num at card_eq
          -- that's impossible, because that would mean that the multiplicity of 2 in 1 is zero, but it's positive
          norm_num [card_eq,
            FiniteMultiplicity.one_right <| (@Nat.finiteMultiplicity_iff 2 1).mpr (by omega)] at mul_2
        -- so consider when R is a single element, r
        · obtain ⟨r, rfl⟩ := Multiset.card_eq_one.mp card_eq
          simp only [Multiset.prod_singleton] at mul_2 mul_3 mul_5 mul_11

          -- we know that r ∈ [1, 33]
          have r_mem : r ∈ Multiset.Icc 1 33 := S_sub (Fin.last _) (by norm_num [hR])

          -- which means that r is non-zero
          have r_eq := ne_zero r r_mem

          -- and the primefactors of r include 2, 3, 5 and 11
          have subs : {2, 3, 5, 11} ⊆ r.primeFactors := by
            intro x xh
            norm_num at xh
            rcases xh with rfl | rfl | rfl | rfl
            all_goals
            · norm_num [r_eq]
              exact dvd_of_multiplicity_pos (by tauto)

          -- so r is larger than 33
          have r_gt : 33 < r := by
            calc 33
            -- the product of 2, 3, 5 and 11 is larger than 33
            _ < ∏ i ∈ {2, 3, 5, 11}, i := by norm_num

            -- and the product of all primefactors of r is a is at least the product of 2, 3, 5 and 11
            _ ≤ ∏ i ∈ r.primeFactors, i := by
              refine Finset.prod_le_prod_of_subset_of_one_le' subs ?_
              intro i ih ihh
              exact Nat.pos_of_mem_primeFactors ih

            -- which is equal to the product of all primefactors of r, with duplicates removed
            _ = ∏ i ∈ r.primeFactorsList.dedup.toFinset, i := by
              congr 1
              ext x
              norm_num

            -- consider the product over the deduplicated list of primefactors
            _ = r.primeFactorsList.dedup.prod := by
              norm_num [List.prod_toFinset _ (List.nodup_dedup r.primeFactorsList)]

            -- that is at most as large as the product over the list of primefactors, including duplicates
            _ ≤ r.primeFactorsList.prod := by
              apply List.Sublist.prod_le_prod'
              · exact r.primeFactorsList.dedup_sublist
              · intro a ah
                exact Nat.pos_of_mem_primeFactorsList ah

            -- and the product of the list of primefactors of r, is equal to r
            _ = r := Nat.prod_primeFactorsList r_eq


          -- but that's impossible, because r ∈ [1, 33]
          norm_num at r_mem
          linarith
