import Mathlib

/- $:$ Magozinovo A.

A straight stick 2 meters long was sawn into $N$ sticks, the length of each of which is expressed in whole centimeters. For what smallest $N$ can it be guaranteed that, using all the resulting sticks, one can, without breaking them, form the contour of some rectangle? -/
theorem number_theory_160090 :
    IsLeast {N | N ≠ 0 ∧ ∀ S : Multiset ℕ, S.card = N → (∀ s ∈ S, 0 < s) → S.sum = 200 →
                  ∃ A1 A2 B1 B2 : Multiset ℕ, A1 + A2 + B1 + B2 = S
                  ∧ A1.sum = A2.sum ∧ B1.sum = B2.sum
                  ∧ A1 ≠ 0 ∧ A2 ≠ 0
                  ∧ B1 ≠ 0 ∧ B2 ≠ 0} 102 := by
      split_ands
      -- 102 is non-zero
      · omega

      -- If we have a collection of 102 sticks with a total length of 200 cm, we can construct a rantangle using all the sticks
      · intro S hS S_pos S_sum

        -- if we have more than 100 sticks with a total length at most 200, then one stick has length 1
        have has_one (M : Multiset ℕ) (hM1 : 100 < M.card) (hM2 : M.sum ≤ 200)
          (hM3 : ∀ m ∈ M, 0 < m) : 1 ∈ M := by

            -- assume we don't have a stick of length 1
            by_contra hh

            -- Then every stick has a length of at least 2
            replace hM3 : ∀ m ∈ M, 2 ≤ m := by
              intro m hm
              specialize hM3 m hm
              have m_ne : m ≠ 1 := ne_of_mem_of_not_mem hm hh
              omega

            -- so the total sum of lengths is larger than 200
            have lt : 200 < M.sum := by
              have sum_ltt : M.card * 2 ≤ M.sum := by
                trans (List.replicate (M.card) 2).sum
                · norm_num
                trans M.toList.sum
                · refine List.Forall₂.sum_le_sum ?_
                  rw [List.forall₂_iff_get]
                  norm_num
                  intro i ih
                  apply hM3
                  simp only [←Multiset.mem_toList, List.getElem_mem]
                simp
              linarith
            -- but that's impossible
            linarith

        -- So we have two sticks of length 1. Separate them out from the rest of the sticks
        obtain ⟨S, rfl⟩ : ∃ R, S = 1 ::ₘ R
          := Multiset.exists_cons_of_mem <| has_one S (by omega) (by omega) S_pos
        norm_num at S_sum S_pos hS
        obtain ⟨S, rfl⟩ : ∃ R, S = 1 ::ₘ R
          := Multiset.exists_cons_of_mem <| has_one S (by omega) (by omega) S_pos

        norm_num at S_sum S_pos hS

        -- Then we have 100 sticks
        have S_card : S.card = 100 := by omega

        -- consider listing out all sticks S' = a_1, a_2, ... a_100
        let S' := S.toList

        -- Take partial sums
        -- A'_1 = a_1
        -- A'_2 = a_1 + a_2
        -- A'_3 = a_1 + a_2 + a_3
        -- etc.
        let A' : ℕ → ℕ := fun i => (S'.take i).sum

        -- let A_i be the partial sum modulo 99
        let A : ℕ → ℕ := (A' · % 99)

        -- We have 100 different partial sums which take 99 different values
        have maps : ∀ a ∈ Finset.Icc 1 100, A a ∈ Finset.Ico 0 99 := by
          norm_num [A]
          omega

        -- so there must be two partial sums which take the same value modulo 99
        obtain ⟨y, y1, y2⟩ := Finset.exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to (b := 1) maps (by norm_num)
        norm_cast at y2

        -- let those partial sums be A' p = A' q, where 1 ≤ p < q ≤ 100
        obtain ⟨k, l, hk, lh, h1, h2⟩ : ∃ p q, 1 ≤ p ∧ q ≤ 100 ∧ A p = A q ∧ p < q := by
          obtain ⟨p, ph, q, qh, hh⟩ := Finset.one_lt_card.mp y2
          norm_num at ph qh
          rcases Nat.lt_or_gt_of_ne hh with hh | hh
          · refine ⟨p, q, ?_, ?_, ?_, hh⟩ <;> linarith
          · refine ⟨q, p, ?_, ?_, ?_, hh⟩ <;> linarith

        -- then A' l - A' k ≡ 0 (mod 99)
        have sub_mod : A' l - A' k ≡ 0 [MOD 99]
          := Nat.sub_mod_eq_zero_of_mod_eq h1.symm


        -- i.e. 99 divides A' l - A' k
        have dvd_99 : 99 ∣ A' l - A' k := Nat.dvd_of_mod_eq_zero sub_mod

        -- The first k values of S' is nonempty
        have take_ne_nil : List.take k S' ≠ [] := by
          simp
          split_ands
          -- because k ≠ 0
          · omega
          -- and S' is nonempty
          · simp [S']
            apply_fun Multiset.card
            simp only [Multiset.card_zero]
            omega

        -- but A' l - A' k < 198
        have lee : A' l - A' k < 198 := by
          unfold A'

          -- A' l coult at most be the sum of all sticks
          have lee : (List.take l S').sum - (List.take k S').sum
            ≤ S'.sum - (List.take k S').sum := by
              gcongr
              apply List.Sublist.sum_le_sum
              exact List.take_sublist l S'
              norm_num
          refine lt_of_le_of_lt lee ?_

          -- and the total length of all sticks is 198
          have sum_eq : S'.sum = 198 := by
            norm_num [S']
            omega
          rw [sum_eq]

          -- so we just need to show that A' k is positive
          simp only [tsub_lt_self_iff, Nat.ofNat_pos, true_and]
          apply List.sum_pos
          -- every stick has a positive length
          · intro x xh
            have x_mem : x ∈ S' := List.mem_of_mem_take xh
            norm_num [S'] at x_mem
            exact S_pos x x_mem
          -- and we have a non-zero amount of sticks
          · exact take_ne_nil


        -- the first k sticks of all stick is the same as the first k sticks of the first l sticks of all sticks
        have take_eq : List.take k S' = List.take k (List.take l S') := by
          rw [List.take_take]
          congr
          symm
          -- because k < l
          exact Nat.min_eq_left <| le_of_lt h2

        -- and 0 < A' l - A' k
        have pos : 0 < A' l - A' k := by
          -- we'll show A' k < A' l
          simp
          simp only [A', take_eq]
          apply lt_of_le_of_ne
          -- we have A' k ≤ A' l
          · apply List.Sublist.sum_le_sum
            · exact List.take_sublist _ _
            · norm_num
          -- and A' k ≠ A' l
          -- let T be the first l sticks
          -- then we just need to show that the sum of the first k sticks of T is not equal to the sum of all sticks of T
          · set T := (List.take l S')
            nth_rw 2 [←List.take_append_drop k T]
            simp only [List.sum_append]

            -- we just need to show that the sum of the remaining sticks in T is non-zero
            suffices : (List.drop k T).sum ≠ 0
            · omega

            -- there's a non-zero amount of sticks
            have ne_empty : List.drop k T ≠ [] := by
              simp [List.drop_eq_nil_iff, T, S']
              omega

            -- let's call one of those a
            simp [List.sum_eq_zero_iff]
            obtain ⟨a, ah⟩ := List.exists_mem_of_ne_nil _ ne_empty
            exists a, ah

            -- then a has a non-zero length
            have a_mem_T : a ∈ T := List.mem_of_mem_drop ah
            have a_mem_S' : a ∈ S' := List.mem_of_mem_take a_mem_T
            norm_num [S'] at a_mem_S'
            exact Nat.not_eq_zero_of_lt (S_pos a a_mem_S')

        -- so A' l - A' k = 99
        have eq_99 : A' l - A' k = 99 := by omega

        -- now we can construct the rectangle

        -- let the vertical sides be the sticks of length 1 we separated
        let A1 : Multiset ℕ := {1}
        let A2 : Multiset ℕ := {1}

        -- let one horizontal side consist of the sticks a_(k+1), a_(k+2), .., a_l
        -- and the other side the remaining sticks
        let B1 : Multiset ℕ := S'.take k ++ S'.drop l
        let B2 : Multiset ℕ := (S'.take l).drop k
        exists A1, A2, B1, B2

        -- note that the horizontal side of the sticks a_(k+1), a_(k+2), .., a_l
        -- has a length of 99
        have B2_sum : B2.sum = 99 := by
          rw [←eq_99]
          simp [B2]
          apply Nat.eq_sub_of_add_eq
          unfold A'
          rw [take_eq, add_comm, ←Nat.sum_append,
            List.take_append_drop]


        -- If we combine all sticks for the horizontal sides, we get all sticks (ignoring the separated sticks of size 1)
        have B1_add_B2 : B1 + B2 = S := by
          unfold B1 B2
          trans ↑(List.drop l S' ++ List.take k S') + ↑(List.drop k (List.take l S'))
          · congr 1
            ext x
            norm_num
            omega
          trans List.drop l S' ++ List.take k S' ++ List.drop k (List.take l S')
          · ext i
            norm_num

          trans Multiset.ofList S'
          · rw [take_eq, List.append_assoc]
            simp
            trans List.take l S' ++ List.drop l S'
            · exact List.perm_append_comm

            simp

          norm_num [S']

        -- Then we can prove that it's a valid rectangle
        split_ands
        -- we used all the sticks
        · unfold A1 A2
          simp
          exact B1_add_B2

        -- the vertical sides have equal length
        · norm_num [A1, A2]

        -- the horizontal sides have equal length
        · apply_fun Multiset.sum at B1_add_B2
          simp at B1_add_B2
          omega
        -- The vertical sides contain sticks
        · norm_num [A1]
        · norm_num [A2]
        -- The horizontal sides contain sticks
        · simpa only [ne_eq, Multiset.coe_eq_zero,
            not_and, not_le, B1] using List.append_ne_nil_of_left_ne_nil take_ne_nil _
        · simp [B2, S']
          omega

      -- then we'll show that 102 is a lower bound
      · simp only [mem_lowerBounds, Set.mem_setOf_eq]
        intro N ⟨N_zero, hh⟩

        -- assume we have some N ≠ 0 which is less than 102, for which all collections of N sticks can create a rectangle
        by_contra N_le
        norm_num at N_le

        -- We'll consider one long stick of size x = 201 - N and N - 1 small sticks of 1 cm each
        set x := 201 - N

        -- every stick will still have a non-zero size
        have pos : ∀ s ∈ x ::ₘ Multiset.replicate (N - 1) 1, 0 < s := by
          intro s sh
          norm_num [Multiset.mem_replicate] at sh
          omega

        -- the total length is 200
        have sum : (x ::ₘ Multiset.replicate (N - 1) 1).sum = 200 := by
          simp
          omega

        specialize hh (x ::ₘ (Multiset.replicate (N - 1) 1)) (by norm_num; omega) pos sum
        obtain ⟨A1, A2, B1, B2, hSum, hA, hB, hA1, hA2, hB1, hB2⟩ := hh

        -- the large stick of length x is on one of the sides
        have x_mem : x ∈ A1 + A2 + B1 + B2 := by
          rw [hSum]
          exact Multiset.mem_cons_self x _
        simp at x_mem

        -- so either the vertical or horizontal sides have a length of at least 100
        have mem_cases : 100 ≤ A1.sum ∨ 100 ≤ B1.sum := by
          rcases x_mem with ((hh | hh) | hh) | hh
          · exact Or.inl <| le_trans (by omega) <| Multiset.le_sum_of_mem hh
          · exact Or.inl <| hA ▸ (le_trans (by omega) <| Multiset.le_sum_of_mem hh)
          · exact Or.inr <| le_trans (by omega) <| Multiset.le_sum_of_mem hh
          · exact Or.inr <| hB ▸ (le_trans (by omega) <| Multiset.le_sum_of_mem hh)

        simp [←hSum] at sum

        -- But a vertical side is a subset (including duplicates) of all sticks
        have A1_subs : A1 ≤ x ::ₘ Multiset.replicate (N - 1) 1 := by
          rw [←hSum]
          trans A1 + A2 + B1
          trans A1 + A2
          · exact Multiset.le_add_right A1 A2
          · exact Multiset.le_add_right (A1 + A2) B1
          · exact Multiset.le_add_right (A1 + A2 + B1) B2

        -- which means it has a positive length
        have A1_sum : 0 < A1.sum := by
          obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hA1
          have a_pos : 0 < a := pos a <| Multiset.mem_of_le A1_subs ha
          exact lt_of_lt_of_le a_pos <| Multiset.le_sum_of_mem ha

        -- similarly for a horizontal side
        have B1_subs : B1 ≤ x ::ₘ Multiset.replicate (N - 1) 1 := by
          rw [←hSum]
          trans A1 + A2 + B1
          · exact Multiset.le_add_left B1 (A1 + A2)
          · exact Multiset.le_add_right (A1 + A2 + B1) B2
        have B1_sum : 0 < B1.sum := by
          obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hB1
          have a_pos : 0 < b := pos b <| Multiset.mem_of_le B1_subs hb
          exact lt_of_lt_of_le a_pos <| Multiset.le_sum_of_mem hb

        -- but then we can't form a rectangle, because the perimeter would be too large
        omega
