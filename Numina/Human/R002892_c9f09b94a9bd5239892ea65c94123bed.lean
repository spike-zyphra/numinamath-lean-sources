import Mathlib

/- Example 1 Place a strictly increasing sequence of $n$ numbers in the first row, and after making some adjustments to the positions of these $n$ numbers, place them in the second row. Then add the corresponding elements of these two rows, and place the new sequence obtained in the third row. It is known that the $n$ numbers in the third row are still strictly increasing. Prove that the first row and the second row are the same. -/
theorem algebra_126895 {n : ℕ} (a b : Fin n → ℝ)
    (ha : StrictMono a) (hb : ∃ p : Equiv.Perm (Fin n), ∀ i, b i = a (p i))
    (hc : StrictMono (fun i => a i + b i)) :
    ∀ i, a i = b i := by
    -- We'll prove it by induction on n, the length of the sequence
    induction' n with x xh2
    -- base case is trivial
    · norm_num
    · intro i
      -- let pp be the mapping between
      obtain ⟨pp, ph⟩ := hb

      -- then the second sequence b is a ∘ pp
      obtain ⟨rfl⟩ : b = a ∘ pp := by
        ext i
        exact ph i
      clear ph

      -- we have that the first element in both rows are the same, i.e. pp 0 = 0
      have zero_case : pp 0 = 0 := by

        -- assume the opposite
        by_contra nee

        -- then there is some m, such that...
        let m := pp.symm 0
        -- ... 0 < m ...
        have m_pos : 0 < m := by
          refine Fin.pos_iff_ne_zero.mpr ?_
          apply_fun pp
          norm_num [m]
          tauto

        -- .. and a 0 = b m
        have a_zero_eq : a 0 = (a ∘ pp) m := by
          norm_num [m]

        -- then we have a i + b i < a m + b m for all i < m
        have lt_first : ∀ i < m, a i + (a ∘ pp) i < a m + (a ∘ pp) m := by
          intro i ih
          exact hc ih

        -- that means that b i < a m for all i < m
        have lt_second : ∀ i < m, (a ∘ pp) i < a m := by
          intro i ih
          have app := lt_first i ih
          rw [←a_zero_eq] at app

          have a_zero_le : a 0 ≤ a i := by
            apply ha.monotone
            norm_num

          linarith

        -- that means that pp i < m for all i < m
        have lt_third : ∀ i < m, pp i < m := by
          intro i ih
          have app := lt_second i ih
          simp at app
          exact (StrictMono.lt_iff_lt ha).mp (lt_second i ih)

        -- we also have 0 < m
        -- expressed as sets, we have {0} ∪ (pp [0, m)) ⊆ [0, m)
        have is_sub : (insert 0 ((Finset.Ico 0 m).map pp.toEmbedding)) ⊆ Finset.Ico 0 m := by
          intro x
          norm_num
          rintro (h1 | h2)
          · exact h1 ▸ m_pos
          · simpa only [Equiv.apply_symm_apply] using lt_third _ h2

        -- which means the LHS set is at most as large as the RHS set.
        have card_le : (insert 0 ((Finset.Ico 0 m).map pp.toEmbedding)).card ≤ (Finset.Ico 0 m).card
          := Finset.card_le_card is_sub

        -- but the RHS set has m elements
        have right_card : (Finset.Ico 0 m).card = m := by norm_num

        -- while the LHS has m + 1 elements
        have left_card : (insert 0 ((Finset.Ico 0 m).map pp.toEmbedding)).card = 1 + m := by
          norm_num
          ring

        -- contradiction
        linarith

      -- now we can prove that a i = b i by considering 0 seperately
      induction' i using Fin.cases with ii
      -- it's the case we proved previously
      · norm_num [zero_case]
      -- we'll show that the others are equal by using the induction hypothesis from the induction on n
      -- the rest a values are ordered, i.e. strictly monotone
      · have tail_strictmono : StrictMono (Fin.tail a) := by
          intro p q pq
          apply ha
          exact Fin.succ_lt_succ_iff.mpr pq

        -- for the rest of the elements, the second row is a permutation of the first row
        have mapp : ∃ p : Equiv.Perm (Fin x), ∀ (i : Fin x), Fin.tail (a ∘ pp) i = Fin.tail a (p i) := by

          refine ⟨?_, ?_⟩
          -- we'll construct the bijection manually
          · refine ⟨?_, ?_, ?_, ?_⟩
            -- forward direction
            · intro j
              -- we increase the index by one, map using pp, then subtract by one
              -- it's okay to subtract by one because the mapping is never 0
              have ne_zero : pp j.succ ≠ 0 := by
                -- we know that only 0 maps to 0
                rw [←zero_case]
                simpa only [ne_eq, EmbeddingLike.apply_eq_iff_eq] using Fin.succ_ne_zero j
              exact (pp j.succ).pred ne_zero
            · intro j
              -- we increase the index by one, map using the inverse of pp, then subtract by one
              -- it's okay to subtract by one because the mapping is never 0
              have ne_zero : pp.symm j.succ ≠ 0 := by
                apply_fun pp
                simpa only [Equiv.apply_symm_apply, zero_case] using Fin.succ_ne_zero j
              exact (pp.symm j.succ).pred ne_zero
            -- it's a left inverse
            · intro i
              norm_num
            -- it's a right inverse
            · intro i
              norm_num
          norm_num [Fin.tail]

        -- the rest of the elements in the third row is strictly monotone
        have lower_strictmono : (StrictMono fun i => Fin.tail a i + Fin.tail (a ∘ pp) i) := by
          intro p q pq
          apply hc
          exact Fin.succ_lt_succ_iff.mpr pq

        apply xh2 (Fin.tail a) (Fin.tail (a ∘ pp)) tail_strictmono mapp lower_strictmono