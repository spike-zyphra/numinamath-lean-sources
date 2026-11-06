import Mathlib

open Finset Real

/- 3. Given positive integers $n, k(k \leqslant n-2)$. Let the set of real numbers $\left\{a_{1}, a_{2}, \cdots, a_{n}\right\}$ be such that the absolute value of the sum of any $k$-element subset does not exceed 1. Prove: If $\left|a_{1}\right| \geqslant 1$, then for any $i(2 \leqslant i \leqslant n)$, we have
$$
\left|a_{1}\right|+\left|a_{i}\right| \leqslant 2 .
$$
(Cold Gangsong, problem contributor) -/
theorem inequalities_137418 {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n - 2)
    (a : Fin n → ℝ) (h : ∀ s, s.card = k → |∑ i ∈ s, a i| ≤ 1) (ha : |a ⟨0, hn⟩| ≥ 1) :
    ∀ i ∈ Ioi ⟨0, hn⟩, |a ⟨0, hn⟩| + |a i| ≤ 2 := by
  by_cases hk' : k = 1
  · intro i hi
    simp [hk'] at h
    have : ({⟨0,hn⟩} : Finset <| Fin n).card = 1 := by simp
    apply h _ at this
    simp at this
    apply le_trans (add_le_add_right this _)
    have : ({i} : Finset <| Fin n).card = 1 := by simp
    apply h _ at this
    simp at this
    apply le_trans (add_le_add_left this _)
    norm_num
  · have hk' : k ≥ 2 := by
      by_contra hk
      simp at hk
      interval_cases k
      simp at hk'
    -- Without loss of generality, assume $a_{1} \geqslant 1$.
    wlog ha0_pos : a ⟨0, hn⟩ ≥ 0 generalizing a with H
    · let a' := -a
      -- Define a' as the negation of a.
      have h' : ∀ s, s.card = k → |∑ i ∈ s, a' i| ≤ 1 := by
        -- The condition still holds for a'.
        intro s hs
        simp [a']
        exact h s hs
      have ha' : |a' ⟨0, hn⟩| ≥ 1 := by
        simp [a']
        exact ha
      obtain H := H a' h' ha'
      simp [a'] at H
      simp
      apply H
      apply le_of_lt
      exact lt_of_not_ge ha0_pos
    · rw [abs_of_nonneg ha0_pos] at ha ⊢
      intro i hi
      -- To prove the conclusion, it suffices to show that for any $j(2 \leqslant j \leqslant n)$, we have:
      -- $$ a_{j} \geqslant a_{1}-2, \text{ and } a_{j} \leqslant 2-a_{1}. $$
      suffices hle : a i ≤ 2 - a ⟨0, hn⟩ ∧ a ⟨0, hn⟩ ≤ 2 + a i
      · apply add_le_of_le_sub_left
        simp [abs]
        exact hle
      · -- Let $[n] = \{1, 2, \cdots, n\}$.
        constructor
        pick_goal 2
        · -- First, prove $a_{j} \geqslant a_{1}-2$.
          -- Let $2 \leqslant j \leqslant n$, and consider two $k$-element subsets $I$ and $J$ of $[n]$ such that $I \backslash J = \{1\}$ and $J \backslash I = \{j\}$.
          have hcard : (univ \ {⟨0, hn⟩, i}).card ≥ k := by
            -- The remaining elements after removing $1$ and $j$ must still have at least $k$ elements.
            rw [card_sdiff]
            · simp
              apply le_trans hkn
              apply Nat.sub_le_sub_left
              apply le_trans (Finset.card_insert_le _ _)
              simp
            · simp
          have hcard' : (univ \ {⟨0, hn⟩, i}).card ≥ k - 1 := by
            -- The remaining elements must also have at least $k-1$ elements.
            apply le_trans ?_ hcard
            simp
          obtain ⟨K, hK1, hK2⟩ := Finset.exists_subset_card_eq hcard'
          let I := K ∪ {⟨0, hn⟩}
          let J := K ∪ {i}
          have hI : I.card = k := by
            -- The cardinality of $I$ is $k$.
            rw [card_union_of_disjoint]
            · simp [hK2]
              rw [Nat.sub_add_cancel hk]
            · apply disjoint_of_subset_left hK1
              symm
              apply disjoint_sdiff_iff_le ?_ ?_ |>.mpr
              all_goals simp
          have hJ : J.card = k := by
            -- The cardinality of $J$ is $k$.
            rw [card_union_of_disjoint]
            · simp [hK2]
              rw [Nat.sub_add_cancel hk]
            · apply disjoint_of_subset_left hK1
              simp
          -- By the condition, $\sum_{s \in I} a_{s} \leqslant 1$ and $\sum_{s \in J} a_{s} \geqslant -1$.
          apply h _ at hI
          apply h _ at hJ
          unfold I at hI
          unfold J at hJ
          simp [abs] at hI hJ
          obtain hI := hI.1
          obtain hJ := hJ.2
          rw [Finset.sum_union] at hI hJ
          · simp at hI hJ
            -- Subtracting these two inequalities gives:
            -- $$ a_{1} - a_{j} \leqslant 2 \Rightarrow a_{j} \geqslant a_{1} - 2. $$
            apply add_le_add hI at hJ
            apply sub_nonneg.mpr at hJ
            apply sub_nonneg.mp
            apply le_of_le_of_eq hJ
            ring
          · apply disjoint_of_subset_left hK1
            simp
          · apply disjoint_of_subset_left hK1
            simp
        · -- Next, prove $a_{j} \leqslant 2-a_{1}$.
          -- Let $S = \{i \in [n] \mid a_{i} > 0\}$.
          let S := univ.filter (fun i => a i > 0)
          have hmem_S : ⟨0, hn⟩ ∈ S := by
            -- $1$ is in $S$ because $a_{1} > 0$.
            simp [S]
            positivity
          -- Assume $|S| \geqslant k$, and take a $k$-element subset $I$ of $S$ such that $1 \in I$.
          -- By the condition, $$ 0 < \sum_{s \in I \setminus \{1\}} a_{s} \leqslant 1 - a_{1} \leqslant 0, $$
          have hS_card : S.card ≤ k - 1 := by
            -- This leads to a contradiction, so $|S| \leqslant k-1$.
            by_contra hcard
            simp at hcard
            have : S.card ≥ k := by exact Nat.le_of_pred_lt hcard
            have hcard : (S \ {⟨0, hn⟩}).card ≥ k - 1 := by
              rw [card_sdiff]
              · simp
                rw [Nat.sub_add_cancel]
                · exact this
                · apply le_trans hk this
              · simp [hmem_S]
            obtain ⟨I, hI1, hI2⟩ := Finset.exists_subset_card_eq hcard
            let S' := I ∪ {⟨0, hn⟩}
            have hS' : S'.card = k := by
              rw [card_union_of_disjoint]
              · simp [hI2]
                rw [Nat.sub_add_cancel hk]
              · apply disjoint_of_subset_left hI1
                simp
            apply h _ at hS'
            unfold S' at hS'
            rw [abs_sum_of_nonneg] at hS'
            rw [sum_union] at hS'
            · simp at hS'
              have : ∑ x ∈ I, a x ≤ 0 := by linarith only [hS', ha]
              have : ∑ x ∈ I, a x > 0 := by
                apply Finset.sum_pos
                · intro i hi
                  apply hI1 at hi
                  simp [S] at hi
                  exact hi.1
                · by_contra h
                  simp at h
                  simp [h] at hI2
                  have : k ≤ 1 := by exact Nat.le_of_sub_eq_zero (id (Eq.symm hI2))
                  linarith only [this, hk']
              linarith
            · apply disjoint_of_subset_left hI1
              simp
            · intro i hi
              simp at hi
              rcases hi with hi | hi
              · apply hI1 at hi
                simp [S] at hi
                exact le_of_lt hi.1
              · rw [hi]
                positivity
          -- Hence, $|[n] \setminus (S \cup \{j\})| \geqslant n-k \geqslant 2$.
          have hcard : (univ \ (S ∪ {i})).card ≥ 2 := by
            trans n - k
            · rw [card_sdiff, card_univ, Fintype.card_fin]
              apply Nat.sub_le_sub_left
              · apply le_trans (card_union_le _ _)
                simp
                apply le_trans (add_le_add_right hS_card _)
                rw [Nat.sub_add_cancel hk]
              · simp
            · trans n - (n - 2)
              · rel [hkn]
              · apply Nat.le_sub_of_add_le
                rw [Nat.add_sub_cancel']
                apply le_trans hk'
                apply le_trans hkn
                simp
          -- Therefore, there exist $i' \neq j' \in [n] \setminus \{1, j\}$ such that $a_{i'} \leqslant 0$ and $a_{j'} \leqslant 0$.
          obtain ⟨I, hI1, hI2⟩ := Finset.exists_subset_card_eq hcard
          obtain ⟨i', j', hne, heq⟩ := card_eq_two.mp hI2
          simp [heq] at hI1
          have hi' : a i' ≤ 0 := by
            -- $a_{i'} \leqslant 0$ because $i' \notin S$.
            have : i' ∈ ({i', j'} : Finset _) := by simp
            apply hI1 at this
            simp [S] at this
            exact this.1
          have hj' : a j' ≤ 0 := by
            -- $a_{j'} \leqslant 0$ because $j' \notin S$.
            have : j' ∈ ({i', j'} : Finset _) := by simp
            apply hI1 at this
            simp [S] at this
            exact this.1
          -- Now, consider two $k$-element subsets $I$ and $I'$ of $[n]$ such that $I \setminus I' = \{1, j\}$ and $I' \setminus I = \{i', j'\}$.
          have hcard : (univ \ {⟨0, hn⟩, i, i', j'}).card ≥ k - 2 := by
            rw [card_sdiff]
            · simp
              apply le_trans hkn
              simp
              rw [Nat.add_assoc, ←Nat.sub_add_comm]
              · simp
                trans n + 4 - 4
                · simp
                · apply Nat.sub_le_sub_left
                  exact card_le_four
              · trans 4
                · exact card_le_four
                · trans k + 2
                  · trans 2 + 2
                    · simp
                    · simp [hk']
                  · apply Nat.add_le_of_le_sub
                    · apply le_trans hk'
                      apply le_trans hkn
                      simp
                    · exact hkn
            · simp
          obtain ⟨I, hI1, hI2⟩ := Finset.exists_subset_card_eq hcard
          let I' := I ∪ {⟨0, hn⟩, i}
          let J' := I ∪ {i', j'}
          -- By the condition, $\sum_{s \in I'} a_{s} \leqslant 1$ and $\sum_{s \in J'} a_{s} \geqslant -1$.
          have hI'_card : I'.card = k := by
            rw [card_union_of_disjoint]
            · simp [hI2]
              trans k - 2 + 2
              · simp
                apply card_eq_two.mpr
                use ⟨0, hn⟩, i
                simp
                simp at hi
                exact Fin.ne_of_lt hi
              · rw [Nat.sub_add_cancel hk']
            · apply disjoint_of_subset_left hI1
              simp
          have hJ'_card : J'.card = k := by
            rw [card_union_of_disjoint]
            · simp [hI2]
              trans k - 2 + 2
              · simp
                apply card_eq_two.mpr
                use i', j'
              · rw [Nat.sub_add_cancel hk']
            · apply disjoint_of_subset_left hI1
              simp
          apply h _ at hI'_card
          apply h _ at hJ'_card
          unfold I' at hI'_card
          unfold J' at hJ'_card
          rw [sum_union] at hI'_card hJ'_card
          rw [sum_insert] at hI'_card hJ'_card
          simp [abs] at hI'_card hJ'_card
          obtain hI' := hI'_card.1
          obtain hJ' := hJ'_card.2
          apply neg_le_iff_add_nonneg.mp at hJ'
          -- Subtracting these two inequalities gives:
          -- $$ a_{j} + a_{1} - a_{i'} - a_{j'} \leqslant 2. $$
          apply add_le_add hI' at hJ'
          apply sub_nonneg.mpr at hJ'
          apply sub_nonneg.mp
          apply le_trans hJ'
          apply sub_nonneg.mp
          ring_nf
          linarith only [hi', hj']
          -- Hence, $a_{j} \leqslant 2-a_{1}+a_{i'}+a_{j'} \leqslant 2-a_{1}$.
          · simp [hne]
          · simp at hi ⊢
            exact Fin.ne_of_lt hi
          · apply disjoint_of_subset_left hI1
            simp
          · apply disjoint_of_subset_left hI1
            simp
