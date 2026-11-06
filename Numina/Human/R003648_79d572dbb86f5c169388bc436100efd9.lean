import Mathlib

/- Shapovalov A.V.

The weight of each weight in the set is a non-integer number of grams. They can balance any integer weight from 1 g to 40 g (weights are placed on one pan of the scales, the weight to be measured - on the other). What is the smallest number of weights in such a set? -/
theorem number_theory_203866 :
  IsLeast ((fun S => Finset.card S) '' {S : Finset ℝ | (∀ x ∈ S, ¬∃ z : ℤ, x = z) ∧ (∀ w ∈ Finset.Icc (1 : ℕ) 40, ∃ T ⊆ S, ∑ i ∈ T, i = w) }) 7
  := by
    -- let P be the set which we want to find the minimum of
    set P := ((fun S => Finset.card S) '' {S : Finset ℝ | (∀ x ∈ S, ¬∃ z : ℤ, x = z) ∧ (∀ w ∈ Finset.Icc (1 : ℕ) 40, ∃ T ⊆ S, ∑ i ∈ T, i = w) })
    -- we can find a set of 7 numbers with the desired property
    have seven_mem : 7 ∈ P := by
      unfold P
      -- consider the numbers [1 / 3, 2 / 3, 4 / 3, .., 2 ^ 6 / 3]
      simp only [not_exists, and_imp, Set.mem_image, Set.mem_setOf_eq]

      -- we construct it as an embedding from [0, 7) to real numbers
      let pow_emb : ℕ ↪ ℕ := ⟨(2 ^ ·), Nat.pow_right_injective <| le_refl 2⟩
      let div_map : ℝ ↪ ℝ := ⟨(· / 3), mul_left_injective₀ (by norm_num)⟩

      let H' : Finset ℝ := ((Finset.range 7).map pow_emb).map Nat.castEmbedding
      let H := H'.map div_map

      exists H
      -- we prove the properties separately
      split_ands
      -- each value is a non-integer
      · intro x xh z
        -- we'll show that 2 ^ i / 3 can't be an integer,
        -- i.e. for every z, 2 ^ i / 3 does not equal z
        simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk,
          Nat.castEmbedding_apply, exists_exists_and_eq_and, Nat.cast_pow, Nat.cast_ofNat, H, H', div_map,
          pow_emb] at xh
        obtain ⟨i, h1, rfl⟩ := xh

        rw [div_eq_iff (by norm_num)]
        -- normalize
        norm_cast
        push_cast

        -- consider mod 3 of both sides
        -- 3 divides the LHS
        apply_fun (3 ∣ ·)
        -- simplify
        norm_num
        norm_cast

        -- assume that 3 divides 2 ^ i
        by_contra hh

        -- then 3 is equal to 2, because they are both prime
        have := Nat.prime_eq_prime_of_dvd_pow Nat.prime_three Nat.prime_two hh

        -- but that's a contradiction
        tauto
      -- for every value w ∈ [1, 40], there's a subset of the numbers which sum to w
      · unfold H

        -- we'll show that every value w ∈ [1, 2 ^ 7 - 1] has a representation as sum of subset of [1, 2, 4, 8, .., 2 ^ 6]
        suffices hm : ∀ w ∈ Finset.Icc (1 : ℕ) (2 ^ 7 - 1), ∃ T ⊆ (Finset.range 7).map pow_emb, ∑ i ∈ T, i = ↑w
        · intro w wh
          have mem_mul : w * 3 ∈ Finset.Icc 1 (2 ^ 7 - 1) := by
            simp only [Nat.reduceMul, Finset.mem_Icc] at wh ⊢
            omega
          obtain ⟨T, T_sub, T_sum⟩ := hm (w * 3) mem_mul
          exists (T.map Nat.castEmbedding).map div_map
          constructor
          · unfold H'
            gcongr
          · simp only [Finset.sum_map, Function.Embedding.coeFn_mk, Nat.castEmbedding_apply,
            div_map]
            rw [←Finset.sum_div, ←Nat.cast_sum, T_sum]
            norm_num

        -- we'll prove it for general 7 = n ≥ 1
        generalize hn : 7 = n
        have pos_n : 1 ≤ n := by omega
        clear hn

        -- we prove it by induction on n
        induction' n, pos_n using Nat.le_induction with n h2 h3
        -- n = 1 is trivial
        · norm_num [pow_emb]
        · intro w wh
          -- consider order cases of 2 ^ n and w
          rcases lt_trichotomy (2 ^ n) w with h4 | h5 | h6
          -- consider when w is larger than 2 ^ n
          -- then we have a representation for w - 2 ^ n
          · have w_mem : w - (2 ^ n) ∈ Finset.Icc 1 (2 ^ n - 1) := by
              simp only [Finset.mem_Icc, tsub_le_iff_right] at wh ⊢
              omega
            obtain ⟨T, T_sub, T_sum⟩ := h3 (w - 2 ^ n) w_mem
            -- then we have a representation for 2 by adding 2 ^ n to the set
            exists insert (pow_emb n) T
            split_ands
            -- it's a subset of possible values
            · trans insert (pow_emb n) ((Finset.range n).map pow_emb)
              · gcongr
              · apply subset_of_eq
                rw [←Finset.map_insert]
                congr
                exact Finset.range_add_one.symm
            -- it sums to w
            -- 2 ^ n is not part of the representation of w - 2 ^ n
            · have not_mem : pow_emb n ∉ T := by
                have not_mem' : pow_emb n ∉ Finset.map pow_emb (Finset.range n) := by norm_num
                exact fun a => not_mem' (T_sub a)
              rw [Finset.sum_insert not_mem, T_sum]
              simp only [Function.Embedding.coeFn_mk, pow_emb]
              omega

          -- 2 ^ n is achievable because 2 ^ n is part of the set
          · subst h5
            -- so consider the set {2 ^ n}
            exists {pow_emb n}
            split_ands
            -- it's a subset of possible values
            · norm_num
            · simp only [Function.Embedding.coeFn_mk, Finset.sum_singleton, pow_emb]

          -- every value less than 2 ^ n has a representation, using the induction hypothesis
          · have w_mem : w ∈ Finset.Icc 1 (2 ^ n - 1) := by
              simp only [Finset.mem_Icc] at wh ⊢
              omega
            obtain ⟨T, T_sub, T_sum⟩ := h3 w w_mem
            exists T
            constructor
            -- it's a subset of possible values
            · refine T_sub.trans ?_
              gcongr
              omega
            · exact T_sum

      -- our chosen set of numbers have 7 numbers
      · simp only [H, H', Finset.card_map, Finset.card_range]

    -- but it's impossible to have a set of 6 numbers with the desired property
    have six_not_mem : ¬6 ∈ P := by
      -- assume that we have 6 such numbers as a set S
      by_contra h
      simp only [not_exists, and_imp, Set.mem_image, Set.mem_setOf_eq, P] at h
      obtain ⟨S, ⟨h1, h2⟩, S_card⟩ := h

      -- we don't care about things being computable here
      classical

      -- let G be all the subsets of our 6 numbers which sum to an integer
      let G := ((Finset.powerset S).image (fun T => ∑ i ∈ T, i)).filter (fun x : ℝ => ∃ z : ℤ, x = z)

      -- it achieves every number in [1, 40]
      have interval_subs : (Finset.Icc 1 40).map Nat.castEmbedding
        ⊆ G
        := by
          intro aa bb
          simp only [G, Finset.mem_filter, Finset.mem_image, Finset.mem_powerset]
          simp only [Finset.mem_map, Nat.castEmbedding_apply] at bb
          obtain ⟨w, wh, rfl⟩ := bb
          have as_subset := h2 w wh
          constructor
          · exact as_subset
          · exists w

      -- S has a positive cardinality
      have S_card_pos : 0 < S.card := by linarith

      -- choose some element a in S
      obtain ⟨a, a_mem⟩ : ∃ a, a ∈ S := by
        refine Finset.Nonempty.exists_mem ?_
        exact Finset.card_pos.mp S_card_pos

      -- then we can split up S into a and (S - a)
      have S_split : insert a (S.erase a) = S := Finset.insert_erase a_mem
      have a_not_mem : ¬a ∈ (S.erase a) := Finset.not_mem_erase a S

      -- consider the mapping from subsets of (S - a), to pairs of sets where you either add a or don't add a
      -- the mapping creates disjoint sets
      have pairwise_dis : ((S.erase a).powerset : Set (Finset ℝ)).PairwiseDisjoint fun t ↦ ({t, insert a t} : Finset (Finset ℝ))
        := by
          intro aa bb cc dd ee
          -- simplify
          simp only [Finset.disjoint_insert_right, Finset.mem_insert, Finset.mem_singleton, not_or,
            Finset.disjoint_singleton_right]
          rw [Finset.mem_coe, Finset.mem_powerset] at bb dd

          have a_mem_cc : a ∈ insert a cc := cc.mem_insert_self a
          have a_nmem_aa : ¬a ∈ aa := fun xx => a_not_mem (bb xx)
          have a_nmem_cc : ¬a ∈ cc := fun xx => a_not_mem (dd xx)
          split_ands
          · exact ee.symm
          · exact Finset.ne_insert_of_not_mem cc aa a_nmem_cc
          · exact ne_of_mem_of_not_mem' a_mem_cc a_nmem_aa
          · by_contra hue
            have subset_1 : insert a cc ⊆ insert a aa := Finset.subset_of_eq hue
            have subset_2 : insert a aa ⊆ insert a cc := Finset.subset_of_eq hue.symm
            rw [Finset.insert_subset_insert_iff a_nmem_cc] at subset_1
            rw [Finset.insert_subset_insert_iff a_nmem_aa] at subset_2
            have eq := subset_antisymm subset_1 subset_2
            exact ee eq.symm

      -- consider the (disjoint) union of all resulting sets
      let as_pairs := Finset.disjiUnion _ _ pairwise_dis

      -- that union is equal to the powerset of S
      have as_pairs_eq : S.powerset = as_pairs := by
        -- an element is part of LHS iff it's part of RHS
        ext x
        -- simplify
        norm_num [as_pairs]
        -- prove both directions separately
        constructor
        · intro xh
          -- consider when a is part of the set
          by_cases a_mem_x : a ∈ x
          · exists x.erase a
            split_ands
            · exact Finset.erase_subset_erase a xh
            · exact Or.inr <| (Finset.insert_erase a_mem_x).symm
          -- and when a is not
          · exists x
            split_ands
            · exact Finset.subset_erase.mpr ⟨xh, a_mem_x⟩
            · tauto
        -- consider when aa is a subset of S - a
        -- then aa and aa + a are both subsets of S
        · rintro ⟨aa, bb, cc | dd⟩
          · rw [cc]
            exact bb.trans <| Finset.erase_subset a S
          · rw [dd]
            refine Finset.insert_subset a_mem ?_
            exact bb.trans <| Finset.erase_subset a S

      -- but then G has at most 32 values
      have G_card : G.card ≤ 32 := by
        simp only [G, as_pairs_eq, Finset.filter_image]
        refine Finset.card_image_le.trans ?_
        unfold as_pairs
        rw [Finset.disjiUnion_eq_biUnion, Finset.filter_biUnion]

        refine Finset.card_biUnion_le.trans ?_
        refine (Finset.sum_le_card_nsmul _ _ 1 ?_).trans ?_
        intro x aa
        rw [Finset.card_le_one]
        intro p ph q qh
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at ph qh
        obtain ⟨ph1, pz, ph2⟩ := ph
        obtain ⟨qh1, qz, qh2⟩ := qh

        rcases ph1 with hh1 | hh2
        · subst hh1
          rcases qh1 with hh3 | hh4
          · tauto
          · subst hh4
            by_cases a_mem_p : a ∈ p
            · simp only [a_mem_p, Finset.insert_eq_of_mem]
            · rw [Finset.sum_insert a_mem_p, ph2] at qh2
              have a_eq : a = ↑(qz - pz : ℤ) := by
                push_cast
                linarith
              have ne := h1 a a_mem (qz - pz)
              contradiction
        · subst hh2
          rcases qh1 with hh3 | hh4
          · subst hh3
            by_cases a_mem_q : a ∈ q
            · simp only [a_mem_q, Finset.insert_eq_of_mem]
            · rw [Finset.sum_insert a_mem_q, qh2] at ph2
              have a_eq : a = ↑(pz - qz : ℤ) := by
                push_cast
                linarith
              have ne := h1 a a_mem (pz - qz)
              contradiction
          · tauto
        simp only [Finset.card_powerset, smul_eq_mul, mul_one]

        have erase_card : (S.erase a).card = S.card - 1
          := Finset.card_erase_of_mem a_mem

        rw [erase_card, S_card]
        norm_num

      -- but [1, 40] has 40 values
      have lhs_card : ((Finset.Icc 1 40).map Nat.castEmbedding : Finset ℝ).card = 40 := by norm_num

      -- so we get 40 ≤ 32
      have card_le := Finset.card_le_card interval_subs

      -- contradiction
      linarith

    -- if it's possible to create a balancing set with i values, then it's possible to do it with (i + 1) values
    have mem_mono : ∀ i, i ∈ P → i.succ ∈ P := by
      intro i h
      simp only [not_exists, and_imp, Set.mem_image, Set.mem_setOf_eq,
        Nat.succ_eq_add_one, P] at h ⊢

      -- let S be the i values which cover [1, 40]
      obtain ⟨S, ⟨h1, h2⟩, h_card⟩ := h

      -- consider the values [π, 2 * π, 3 * π, .., (i + 1)*π]
      let f := (· * Real.pi) ∘ (@Nat.cast ℝ _)
      have f_inj : f.Injective := (mul_left_injective₀ Real.pi_ne_zero).comp CharZero.cast_injective
      let range := (Finset.Icc 1 (i + 1)).map ⟨f, f_inj⟩

      -- it has i + 1 values
      have range_card : range.card = i + 1 := by
        unfold range
        simp only [Finset.card_map, Nat.card_Icc, add_tsub_cancel_right]

      -- which means there's a value in [π, 2 * π, 3 * π, .., (i + 1)*π] that is not in S
      have card_lt : S.card < range.card := by linarith
      have ncard_lt : Set.ncard (S : Set ℝ) < Set.ncard (range : Set ℝ) := by
        simpa only [Set.ncard_coe_Finset] using card_lt

      -- let x be such a value
      obtain ⟨x, x_mem, x_not_mem⟩ := Set.exists_mem_not_mem_of_ncard_lt_ncard ncard_lt
      simp only [Finset.mem_coe] at x_mem x_not_mem

      -- so we have the set S + x
      exists insert x S
      split_ands
      -- none of the values are integers
      · intro y yh z
        simp only [Finset.mem_insert] at yh
        rcases yh with eq | mem
        -- consider when y is a multiple of π
        · subst eq
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk,
            Function.comp_apply, range, f] at x_mem
          obtain ⟨a, ah1, ah2⟩ := x_mem
          rw [←ah2, mul_comm, ←eq_div_iff]
          convert_to ¬Real.pi = (z : ℝ) / ((a : ℤ) : ℝ)

          -- π is irrational, so y is irrational too
          exact (irrational_iff_ne_rational Real.pi).mp irrational_pi _ _

          -- a is positive
          have a_pos : 1 ≤ a := (Finset.mem_Icc.mp ah1).1

          -- so a ≠ 0
          positivity
        · tauto
      -- every w ∈ [1, 40] is achievable
      · intro w wh
        -- we can just us values in S
        obtain ⟨T, hT1, hT2⟩ := h2 w wh
        exists T
        refine ⟨?_, hT2⟩

        -- T ⊆ x + S because T ⊆ S
        exact hT1.trans <| Finset.subset_insert x S
      -- S + x has i + 1 values
      · rw [←h_card]
        exact Finset.card_insert_of_not_mem x_not_mem

    -- so P is an "upper set"
    have mem_le : IsUpperSet P := by
      intro i j le h
      exact Nat.set_induction_bounded h mem_mono le

    -- so 7 is the least value of p
    unfold IsLeast
    refine ⟨seven_mem, ?_⟩
    rw [mem_lowerBounds]
    intro x xh
    -- assume that we can achieve it with some x < 7
    by_contra h
    -- then we can achieve it with 6 values
    have six_mem : 6 ∈ P := mem_le (by omega) xh
    -- but we can't
    contradiction