import Mathlib

/-The natural numbers from 1 to 50 are written down on the blackboard. At least how many of them should be deleted, in order that the sum of any two of the remaining numbers is not a prime?-/
theorem number_theory_60522:
    IsLeast {x | ∃ S, S ⊆ Finset.Icc 1 50 ∧ x = 50 - S.card ∧ ∀ m ∈ S, ∀ n ∈ S, m ≠ n → ¬ Nat.Prime (m + n)} 25 := by
    constructor
    -- Notice that if the odd, respectively even, numbers are all deleted, then the sum of any two remaining numbers is even and exceeds 2, so it is certainly not a prime. 
    -- We prove that 25 is the minimal number of deleted numbers. 
    · use (Finset.Icc 1 50).filter Even
      constructorm* _ ∧ _
      · exact Finset.inter_eq_right.mp rfl
      · exact rfl
      · intro m hm n hn hmn
        simp at hm
        simp at hn

        suffices h: Even (m+n) by
          by_contra h'
          have := Nat.Prime.odd_of_ne_two h' (by omega)
          rw[←Nat.not_even_iff_odd] at this
          exact this h
        rw[Nat.even_add]
        simp only [hm, hn]
    ·
      intro x hx
      obtain ⟨S, h₁, h₂, h₃⟩ := hx
      suffices S.card ≤ 25 by
        omega
      clear h₂ x

      by_contra! h

      let p := 53
      have hp : Nat.Prime p := by decide
      --  We group the positive integers from 1 to 50 in 25 pairs, such that the sum of the numbers within each pair is a prime:
      -- Elements in S that are part of a pair {x, p-x} where both x and p-x are in Icc 1 50
      let A := Finset.filter (fun x : ℕ => p - x ∈ Finset.Icc 1 50) (Finset.Icc 1 50)
      -- Equivalently, A is Icc 3 50
      have A_eq : A = Finset.Icc 3 50 := by
        ext x
        simp only [A, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro h_left
          rcases h_left with ⟨⟨hx1, hx50⟩, ⟨hpx1, hpx50⟩⟩
          constructor
          · refine Nat.succ_le_of_lt (by omega)
          · exact hx50
        · intro h_right
          rcases h_right with ⟨hx3, hx50⟩
          refine ⟨⟨?_, hx50⟩, ⟨?_, ?_⟩⟩ <;> omega

      let S_paired := S.filter (fun x => x ∈ A)
      let S_unpaired := S.filter (fun x => x ∉ A)
      let A_complement := Finset.filter (fun x => x < p - x) A

      have A_complement_eq : A_complement = Finset.Icc 3 26 := by
        ext x
        simp only [A_complement, Finset.mem_filter, Finset.mem_Icc, A_eq]
        constructor
        · intro h
          rcases h with ⟨⟨hx3, hx50⟩, h_lt_p_sub_x⟩
          constructor
          · exact hx3
          · omega
        · intro h
          rcases h with ⟨hx3, hx26⟩
          refine ⟨⟨hx3, by linarith⟩, by omega⟩ 

      have card_S_paired_le : S_paired.card ≤ A_complement.card := by
        -- Show that for each y in A_complement, S_paired can contain at most one of y or p-y
        -- The sum of cardinalities of S_paired intersected with {y, p-y} for y in A_complement
        suffices S_paired.card = (A_complement.biUnion (fun x => S_paired.filter (fun y => y = x ∨ y = p - x))).card by
          have hh: (∀ a ∈ A_complement, {y ∈ S_paired | y = a ∨ y = p - a}.card ≤ 1) := by
            simp only [Finset.card_le_one_iff, A_complement, Finset.mem_filter, and_imp, S_paired, A]

            intro a _ _ _ b c hb₁ _ _ hb₄ hc₁ _ _ hc₄
            rcases hb₄ with rfl | rfl
            rcases hc₄ with rfl | rfl
            · rfl
            · simp_all
              by_contra! h
              specialize h₃ b hb₁ (p-b) hc₁ h
              rw[show b + (p - b) = p by omega] at h₃
              simp only [p] at h₃
              exact h₃ hp
            · rcases hc₄ with rfl | rfl
              simp_all
              by_contra! h
              specialize h₃ (p-c) hb₁ c hc₁ h
              rw[show p - c + c = p by omega] at h₃
              simp only [p] at h₃
              exact h₃ hp
              rfl

          have crd := Finset.card_biUnion_le_card_mul A_complement (fun x => S_paired.filter (fun y => y = x ∨ y = p - x)) 1
          rw [this]
          specialize crd hh
          omega

        have : S_paired = (A_complement.biUnion fun x => {y ∈ S_paired | y = x ∨ y = p - x}) := by
          ext a
          constructor
          · simp[S_paired]
            simp_rw[p]
            intro h₁ h₂
            by_cases h: a ∈ A_complement
            · use a
              constructorm* _ ∧ _
              · exact h
              · exact h₁
              · exact h₂
              · omega
            · use p - a
              constructorm* _ ∧ _
              simp[A, Set.mem_setOf_eq, A_complement, p] at h₂ h ⊢
              · omega
              · exact h₁
              · exact h₂
              · simp[A, A_complement, p] at  h h₂ ⊢
                omega
          · simp_all

        rw[←this]

      have A_complement_card_24 : A_complement.card = 24 := by simp[A_complement_eq]

      have S_unpaired_eq_S_inter_1_2 : S_unpaired = S.filter (fun x => x = 1 ∨ x = 2) := by
        ext x
        simp only [S_unpaired, Finset.mem_filter, A, Finset.mem_Icc, not_and, not_le]
        constructor
        · intro h
          cases h
          rename_i h_mem_S h_not_mem_X_paired
          simp[imp_iff_or_not] at h_not_mem_X_paired
          have x_in_A : x ∈ Finset.Icc 1 50 := Finset.mem_of_subset h₁ h_mem_S
          rw[Finset.mem_Icc] at x_in_A
          rcases x_in_A with ⟨hx1, hx50⟩
          cases h_not_mem_X_paired
          · refine ⟨h_mem_S, ?_⟩
            omega
          · simp [h_mem_S]; omega
        · intro h; cases h; rename_i h_mem_S h_1_or_2
          refine ⟨h_mem_S, ?_⟩
          omega

      have card_S_unpaired_le_1 : S_unpaired.card ≤ 1 := by
        rw [S_unpaired_eq_S_inter_1_2]
        have : 1 ∈ S → ¬ 2 ∈ S := by
          intro h
          by_contra h'
          specialize h₃ 1 h 2 h' (by decide)
          norm_num at h₃
        refine Finset.card_le_one.mpr ?_
        simp only [Finset.mem_filter, and_imp]
        intro a ha ha' b hb hb'
        rcases ha'  with rfl | rfl
        · have := this ha
          suffices b ≠ 2 by
            omega
          by_contra!
          subst this
          exact this hb
        · simp[ha] at this
          suffices b ≠ 1 by
            omega
          by_contra!
          subst this
          exact this hb

      -- Card of S is sum of cards of S_paired and S_unpaired
      have h_card_decomp : S.card = S_paired.card + S_unpaired.card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg S S fun x => x ∈ A)]
        rw [Finset.filter_union_filter_neg_eq (fun x => x ∈ A)]
      omega
