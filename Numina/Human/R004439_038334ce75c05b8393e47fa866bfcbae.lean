import Mathlib

-- If a, b, c are distinct positive real numbers, what is the smallest possible number of distinct numbers among the numbers a+b, b+c, c+a, ab, bc, ca, abc?
theorem algebra_266930 : IsLeast {x | ∃ a b c : ℝ, (a > 0 ∧ b > 0 ∧ c > 0) ∧ (a≠b ∧ a≠c ∧ b≠c) ∧ (∃ s : Finset ℝ, s.card = x ∧
    (a + b ∈ s ∧ b + c ∈ s ∧ c + a ∈ s ∧ a * b ∈ s ∧ b * c ∈ s ∧ c * a ∈ s ∧ a * b * c ∈ s))} 4 := by
      constructor

      -- Part 1: Show that 4 is achievable (construct an example)
      · simp
        -- Choose specific values: a = √2, b = 1+√2, c = 1
        use √2, (1+√2), 1
        simp
        constructor
        · -- Verify all numbers are positive and distinct
          have : √2 > 0 := by simp
          linarith
        · -- Construct the set S with exactly 4 distinct elements
          let S : Finset ℝ := {2*√2 + 1, 1+√2, 2+√2, √2}
          use S
          constructor
          · -- Prove that S has exactly 4 elements by showing all are distinct
            unfold S
            have h1 : (2 * Real.sqrt 2 + 1 : ℝ) ≠ (1 + Real.sqrt 2 : ℝ) := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
            have h2 : (2 * Real.sqrt 2 + 1 : ℝ) ≠ (2 + Real.sqrt 2 : ℝ) := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
            have h3 : (2 * Real.sqrt 2 + 1 : ℝ) ≠ (Real.sqrt 2 : ℝ) := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
            have h4 : (1 + Real.sqrt 2 : ℝ) ≠ (2 + Real.sqrt 2 : ℝ) := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
            have h5 : (1 + Real.sqrt 2 : ℝ) ≠ (Real.sqrt 2 : ℝ) := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
            have h6 : (2 + Real.sqrt 2 : ℝ) ≠ (Real.sqrt 2 : ℝ) := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
            simp [Finset.card_insert_of_not_mem, h1, h2, h3, h4, h5, h6]
          · -- Verify that all 7 expressions belong to S
            -- With our choice: a+b = √2+(1+√2) = 1+2√2, b+c = (1+√2)+1 = 2+√2,
            -- c+a = 1+√2, ab = √2(1+√2) = √2+2, bc = (1+√2)·1 = 1+√2,
            -- ca = 1·√2 = √2, abc = √2(1+√2)·1 = √2+2
            ring_nf
            unfold S
            simp [add_comm, mul_comm]

      -- Part 2: Show that no configuration can have fewer than 4 distinct values
      · unfold lowerBounds
        simp
        -- Assume we have any valid configuration with set S
        intro s a b c ha hb hc hneq1 hneq2 hneq3 S hcard hadd1 hadd2 hadd3 hmul1 hmul2 hmul3 hmul
        -- Prove by contradiction: assume |S| < 4
        by_contra h
        rw [← hcard] at h
        simp at h

        -- Key insight: The three products ab, bc, ca are always distinct
        -- (since a, b, c are distinct and positive)
        have h1 : a * b ≠ b * c := by
          rw [mul_comm]
          intro heq
          have := @mul_left_cancel₀ ℝ _ _ _ _ _ _ (by linarith) heq
          exact hneq2 this
        have h2 : b * c ≠ c * a := by
          rw [mul_comm]
          intro heq
          have := @mul_left_cancel₀ ℝ _ _ _ _ _ _ (by linarith) heq
          exact hneq1 (id (Eq.symm this))
        have h3 : c * a ≠ a * b := by
          rw [mul_comm]
          intro heq
          have := @mul_left_cancel₀ ℝ _ _ _ _ _ _  (by linarith) heq
          exact hneq3 (id (Eq.symm this))

        -- Since ab, bc, ca are distinct, they form a set T of size 3
        let T : Finset ℝ := {a*b, b*c, c*a}
        have hTcard : T.card = 3 := by
          unfold T
          refine Finset.card_eq_three.mpr ?_
          use a * b, b * c, c * a
          simp [h1, h2, h3, Ne.symm]

        -- T is a subset of S (since all products are in S)
        have hsub : T ⊆ S := by
          refine Finset.insert_subset hmul1 ?hs
          refine Finset.insert_subset hmul2 ?hs.hs
          exact Finset.singleton_subset_iff.mpr hmul3

        -- If |S| < 4 and T ⊆ S with |T| = 3, then S = T (since |S| ≥ 3)
        have : S = T := by
          refine (Finset.eq_iff_card_ge_of_superset hsub).mp ?_
          linarith

        -- But this means abc must equal one of ab, bc, or ca
        rw [this] at hmul
        unfold T at hmul
        simp at hmul
        rcases hmul with hcase1 | hcase2 | hcase3

        -- Case 1: abc = ab, which implies c = 1
        · have hceq : c = 1 := by
            nth_rw 2 [← mul_one (a*b)] at hcase1
            exact @mul_left_cancel₀ ℝ _ _ _ (a*b) c 1 (by nlinarith) hcase1
          -- With c = 1, analyze the sums and show contradiction
          simp_rw [hceq] at *
          let T' : Finset ℝ := {b+1, a+1, a+b}
          have hTcard' : T'.card = 3 := by
            apply Finset.card_eq_three.mpr
            use b+1, a+1, a+b
            simp
            constructor
            · exact fun a_1 => hneq1 (id (Eq.symm a_1))
            · constructor
              · intro heq
                rw [add_comm] at heq
                simp at heq
                exact hneq2 (id (Eq.symm heq))
              · exact fun a => hneq3 (id (Eq.symm a))
          have hsub' : T' ⊆ S := by
            refine Finset.insert_subset hadd2 ?hs'
            refine Finset.insert_subset ?hs'.ha ?hs'.hs
            rw [add_comm]
            exact hadd3
            exact Finset.singleton_subset_iff.mpr hadd1
          have : S = T' := by
            apply (Finset.eq_iff_card_ge_of_superset hsub').mp
            linarith
          -- This leads to contradictions in the remaining cases
          unfold T' at this
          simp_rw [this] at *
          simp at hmul2
          simp at hmul3
          rcases hmul2 with h | h
          · rcases hmul3 with _ | _
            · linarith
            · linarith
          · rcases hmul3 with _ | _
            · linarith
            · linarith

        -- Case 2: abc = bc, which implies a = 1 (similar analysis)
        · rcases hcase2 with hcase2 | hcase2
          · have hceq : a = 1 := by
              nth_rw 2 [← mul_one b] at hcase2
              rw [mul_comm] at hcase2
              exact @mul_left_cancel₀ ℝ _ _ _ b a 1 (by nlinarith) hcase2
            simp_rw [hceq] at *
            let T' : Finset ℝ := {c+1, b+1, b+c}
            have hTcard' : T'.card = 3 := by
              apply Finset.card_eq_three.mpr
              use c+1, b+1, b+c
              simp
              constructor
              · exact fun a => hneq3 (id (Eq.symm a))
              · constructor
                · intro heq
                  rw [add_comm] at heq
                  simp at heq
                  exact hneq1 heq
                · exact hneq2
            have hsub' : T' ⊆ S := by
              apply Finset.insert_subset hadd3
              apply Finset.insert_subset
              rw [add_comm]
              exact hadd1
              exact Finset.singleton_subset_iff.mpr hadd2
            have : S = T' := by
              apply (Finset.eq_iff_card_ge_of_superset hsub').mp
              linarith
            unfold T' at this
            simp_rw [this] at *
            simp at hmul1
            simp at hmul3
            rcases hmul1 with h | h
            · rcases hmul3 with _ | _
              · linarith
              · linarith
            · rcases hmul3 with _ | _
              · linarith
              · linarith
          · linarith

        -- Case 3: abc = ca, which implies b = 1 (similar analysis)
        · have hceq : b = 1 := by
            rw [mul_comm, ← mul_assoc] at hcase3
            nth_rw 2 [← mul_one (c*a)] at hcase3
            exact @mul_left_cancel₀ ℝ _ _ _ (c*a) b 1 (by nlinarith) hcase3
          simp_rw [hceq] at *
          let T' : Finset ℝ := {a+1, c+1, c+a}
          have hTcard' : T'.card = 3 := by
            apply Finset.card_eq_three.mpr
            use a+1, c+1, c+a
            simp
            constructor
            · exact hneq2
            · constructor
              · intro heq
                rw [add_comm] at heq
                simp at heq
                exact hneq3 heq
              · exact fun a_1 => hneq1 (id (Eq.symm a_1))
          have hsub' : T' ⊆ S := by
            apply Finset.insert_subset hadd1
            apply Finset.insert_subset
            rw [add_comm]
            exact hadd2
            exact Finset.singleton_subset_iff.mpr hadd3
          have : S = T' := by
            apply (Finset.eq_iff_card_ge_of_superset hsub').mp
            linarith
          unfold T' at this
          simp_rw [this] at *
          simp at hmul1
          simp at hmul2
          rcases hmul1 with h | h
          · rcases hmul2 with _ | _
            · linarith
            · linarith
          · rcases hmul2 with _ | _
            · linarith
            · linarith
