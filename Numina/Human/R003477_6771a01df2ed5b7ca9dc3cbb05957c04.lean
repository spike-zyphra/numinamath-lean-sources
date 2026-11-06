 import Mathlib

-- Problem: Given S ⊆ {1,2,...,12}, |S|=6, and for any a < b in S, b is not a multiple of a.
-- What is the smallest possible element in such an S?

theorem number_theory_186518 :
  (∀ (S : Finset ℕ), S ≤ Finset.Icc 1 12 ∧ S.card = 6 ∧
    (∀ a ∈ S, ∀ b > a, a∣b → b ∉ S) → ∀ s ∈ S, s ≥ 4)
  ∧
  ∃ (S : Finset ℕ), S ≤ Finset.Icc 1 12 ∧ S.card = 6 ∧
    (∀ a ∈ S, ∀ b > a, a∣b → b ∉ S) ∧ IsLeast S 4 := by

  constructor
  -- Part 1: Prove that in any such S, all elements are at least 4.
  · intro S ⟨hS1, hS2, hS3⟩ s hs
    -- Let T be the complement of S in {1..12}
    let T : Finset ℕ := Finset.Icc 1 12 \ S

    -- S can be written as {1..12} minus T
    have hST : S = Finset.Icc 1 12 \ T := by
      exact Eq.symm (Finset.sdiff_sdiff_eq_self hS1)

    -- S and T together cover all of {1..12}
    have : S ∪ T = Finset.Icc 1 12 := by
      exact Finset.union_sdiff_of_subset hS1

    -- The total cardinality splits: |S| + |T| = 12
    have : S.card + T.card = (Finset.Icc 1 12).card := by
      rw [← this]
      refine Eq.symm (Finset.card_union_of_disjoint ?_)
      unfold T
      exact Finset.disjoint_sdiff

    -- Since |S| = 6, |T| = 6 as well
    have hT : T.card = 6 := by
      simp at this
      omega

    -- Show that 1 cannot be in S
    have hone : 1 ∉ S := by
      by_contra hone
      -- If 1 ∈ S, then for any a ≥ 2, a ∉ S (since 1 divides all a)
      have : ∀ a :ℕ, a ≥ 2 ∧ a ≤ 12 → a ∈ T := by
        intro a ha
        have := hS3 1 hone a (by linarith) (by norm_num)
        unfold T
        apply Finset.mem_sdiff.mpr
        constructor
        · simp
          constructor
          · linarith
          · linarith
        · exact this
      -- So T contains {2,3,4,5,6,7,8}
      have : {2, 3, 4, 5, 6, 7, 8} ≤ T := by
        intro x hx
        simp at hx
        rcases hx with h | h | h | h | h | h | h
        · have := this 2 (⟨by linarith, by linarith⟩)
          rw [h]
          exact this
        · have := this 3 (⟨by linarith, by linarith⟩)
          rw [h]
          exact this
        · have := this 4 (⟨by linarith, by linarith⟩)
          rw [h]
          exact this
        · have := this 5 (⟨by linarith, by linarith⟩)
          rw [h]
          exact this
        · have := this 6 (⟨by linarith, by linarith⟩)
          rw [h]
          exact this
        · have := this 7 (⟨by linarith, by linarith⟩)
          rw [h]
          exact this
        · have := this 8 (⟨by linarith, by linarith⟩)
          rw [h]
          exact this
      -- But then T has at least 7 elements, contradicting |T| = 6
      have : T.card ≥ ({2, 3, 4, 5, 6, 7, 8}:Finset ℕ).card := by
        exact Finset.card_le_card this
      simp at this
      linarith

    -- Next, show that 2 cannot be in S (otherwise, too many multiples of 2 must be excluded)
    have htwo : 2 ∉ S := by
      by_contra htwo
      -- If 2 ∈ S, then all even numbers >2 must go to T
      have : {1, 4, 6, 8, 10, 12} ≤ T := by
        intro x hx
        simp at hx
        unfold T
        refine Finset.mem_sdiff.mpr ?_
        constructor
        · rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
          all_goals trivial
        · rcases hx with h | h | h | h | h | h
          · rw [h]
            exact hone
          · rw [h]
            apply hS3 2 htwo 4 (by linarith) (by norm_num)
          · rw [h]
            apply hS3 2 htwo 6 (by linarith) (by norm_num)
          · rw [h]
            apply hS3 2 htwo 8 (by linarith) (by norm_num)
          · rw [h]
            apply hS3 2 htwo 10 (by linarith) (by norm_num)
          · rw [h]
            apply hS3 2 htwo 12 (by linarith) (by norm_num)
      -- T must be exactly those 6 numbers
      have : T = {1, 4, 6, 8, 10, 12} := by
        refine Finset.eq_of_superset_of_card_ge this ?hts
        simp
        linarith
      rw [this] at hST
      -- So S = rest = {2,3,5,7,9,11}
      have hthree : 3 ∈ S := by
        rw [hST]
        simp
      have hnine : 9 ∈ S := by
        rw [hST]
        simp
      -- But 3 divides 9, both in S: contradiction
      apply hS3 3 hthree 9 (by linarith) (by norm_num) hnine

    -- Similarly, show that 3 ∉ S
    have hthree : 3 ∉ S := by
      by_contra hthree
      -- If 3 ∈ S, then all its multiples >3 must go to T
      have : {1, 2, 6, 9, 12} ≤ T := by
        intro x hx
        simp at hx
        unfold T
        refine Finset.mem_sdiff.mpr ?_
        constructor
        · rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
          all_goals trivial
        · rcases hx with h | h | h | h | h
          · rw [h]
            exact hone
          · rw [h]
            exact htwo
          · rw [h]
            apply hS3 3 hthree 6 (by linarith) (by norm_num)
          · rw [h]
            apply hS3 3 hthree 9 (by linarith) (by norm_num)
          · rw [h]
            apply hS3 3 hthree 12 (by linarith) (by norm_num)
      -- Now, consider whether 4 ∈ S or 4 ∈ T
      by_cases hfour : 4 ∈ S
      · -- If 4 ∈ S, then 8 ∈ T
        have height : 8 ∈ T := by
          unfold T
          refine Finset.mem_sdiff.mpr ?_
          constructor
          · trivial
          · apply hS3 4 hfour 8 (by linarith) (by norm_num)
        -- So T contains {1,2,6,9,12,8}
        have : {1, 2, 6, 9, 12} ∪ {8} ≤ T := by
          refine Finset.le_iff_subset.mpr ?_
          exact (Finset.erase_subset_iff_of_mem height).mp this
        have heq : {1, 2, 6, 9, 12} ∪ {8} = ({1, 2, 6, 8, 9, 12} : Finset ℕ) := by
          trivial
        rw [heq] at this
        have : T = {1, 2, 6, 8, 9, 12} := by
          apply Finset.eq_of_superset_of_card_ge this
          simp
          linarith
        rw [this] at hST
        -- S = {3,4,5,7,10,11}
        have hfive : 5 ∈ S := by
          rw [hST]
          simp
        have hten : 10 ∈ S := by
          rw [hST]
          simp
        -- 5 divides 10, both in S: contradiction
        apply hS3 5 hfive 10 (by linarith) (by norm_num) hten
      · -- If 4 ∈ T, then T = {1,2,6,9,12,4}
        have hfour : 4 ∈ T := by
          unfold T
          refine Finset.mem_sdiff.mpr ?_
          constructor
          · trivial
          · exact hfour
        have : {1, 2, 6, 9, 12} ∪ {4} ≤ T := by
          refine Finset.le_iff_subset.mpr ?_
          exact (Finset.erase_subset_iff_of_mem hfour).mp this
        have heq : {1, 2, 6, 9, 12} ∪ {4} = ({1, 2, 6, 4, 9, 12} : Finset ℕ) := by
          trivial
        rw [heq] at this
        have : T = {1, 2, 6, 4, 9, 12} := by
          apply Finset.eq_of_superset_of_card_ge this
          simp
          linarith
        rw [this] at hST
        -- S = {3,5,7,8,10,11}
        have hfive : 5 ∈ S := by
          rw [hST]
          simp
        have hten : 10 ∈ S := by
          rw [hST]
          simp
        -- 5 divides 10, both in S: contradiction
        apply hS3 5 hfive 10 (by linarith) (by norm_num) hten

    -- Therefore, S cannot contain 1, 2, or 3. So the minimal element in S is at least 4.
    by_contra hle
    simp at hle
    rcases hle with h1 | h2 | h3
    · simp at hs
      apply hthree hs
    · simp at hs
      apply htwo hs
    · simp at h3
      have : s ≠ 0 := by
        by_contra hszero
        rw [hszero] at hs
        have : 0 ∈ Finset.Icc 1 12 := by
          exact hS1 hs
        trivial
      have : s = 1 := by omega
      rw [this] at hs
      apply hone hs

  -- Part 2: Construct explicit S with min = 4
  · let S : Finset ℕ := {4, 5, 6, 7, 9, 11}
    use S
    constructor
    · exact right_eq_inf.mp rfl
    · constructor
      · exact rfl
      · constructor
        -- Show that for any a < b in S, b is not a multiple of a
        · intro a ha b hgt hab hb
          unfold S at ha
          unfold S at hb
          simp at ha
          simp at hb
          rcases ha with h1 | h2 | h3 | h4 | h5 | h6
          · rcases hb with hh1 | hh2 | hh3 | hh4 | hh5 | hh6
            · linarith
            · rw [h1, hh2] at hab
              norm_num at hab
            · rw [h1, hh3] at hab
              norm_num at hab
            · rw [h1, hh4] at hab
              norm_num at hab
            · rw [h1, hh5] at hab
              norm_num at hab
            · rw [h1, hh6] at hab
              norm_num at hab
          · rcases hb with hh1 | hh2 | hh3 | hh4 | hh5 | hh6
            · linarith
            · linarith
            · rw [h2, hh3] at hab
              norm_num at hab
            · rw [h2, hh4] at hab
              norm_num at hab
            · rw [h2, hh5] at hab
              norm_num at hab
            · rw [h2, hh6] at hab
              norm_num at hab
          · rcases hb with hh1 | hh2 | hh3 | hh4 | hh5 | hh6
            · linarith
            · linarith
            · linarith
            · rw [h3, hh4] at hab
              norm_num at hab
            · rw [h3, hh5] at hab
              norm_num at hab
            · rw [h3, hh6] at hab
              norm_num at hab
          · rcases hb with hh1 | hh2 | hh3 | hh4 | hh5 | hh6
            · linarith
            · linarith
            · linarith
            · linarith
            · rw [h4, hh5] at hab
              norm_num at hab
            · rw [h4, hh6] at hab
              norm_num at hab
          · rcases hb with hh1 | hh2 | hh3 | hh4 | hh5 | hh6
            · linarith
            · linarith
            · linarith
            · linarith
            · linarith
            · rw [h5, hh6] at hab
              norm_num at hab
          · rcases hb with hh1 | hh2 | hh3 | hh4 | hh5 | hh6
            · linarith
            · linarith
            · linarith
            · linarith
            · linarith
            · linarith
        -- Show 4 is indeed the least element
        · unfold S
          simp
          constructor
          · exact Set.mem_insert 4 {5, 6, 7, 9, 11}
          · simp
