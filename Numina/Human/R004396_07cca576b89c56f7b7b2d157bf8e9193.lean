import Mathlib

set_option maxHeartbeats 500000
theorem algebra_260552 :
  IsLeast {n | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a < b ∧ b < c ∧
  n = Finset.card {a + b, b + c, c + a, a ^ 2 + b ^ 2, b ^ 2 + c ^ 2, c ^ 2 + a ^ 2} } 4 := by

  have : √5 > 0 := by positivity
  let c := (1+√5)/2
  have hc : c^2 = 1 + c := by
    have h2 : c^2 - c - 1 = 0 := by
      unfold c
      ring_nf
      simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      ring
    linarith [h2]
  constructor
  . use 0, 1, c
    simp
    refine ⟨by positivity, ?_, ?_⟩
    . unfold c
      suffices 1 < √5 by linarith
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    . rw [hc]
      simp
      repeat rw [Finset.card_insert_of_not_mem]
      simp
      . by_contra h
        simp at h
      . by_contra h
        simp at h
        rcases h with h1| h2
        . unfold c at h1
          linarith
        . unfold c at h2
          linarith
      . by_contra h
        simp at h
        rcases h with h1| h2
        . unfold c at h1
          have : √5 = 1 := by linarith
          rw [Real.sqrt_eq_cases] at this
          rcases this with h3| h4
          . linarith
          . linarith
        . unfold c at h2
          linarith

  . unfold lowerBounds
    simp
    intro n a ha b hb c hc hab hbc hcard
    by_contra hn
    simp at hn

    let S1 := ({a + b, b + c, c + a} : Finset ℝ)
    let S2 := ({a ^ 2 + b ^ 2, b ^ 2 + c ^ 2, c ^ 2 + a ^ 2} : Finset ℝ)
    let S := ({a + b, b + c, c + a, a ^ 2 + b ^ 2, b ^ 2 + c ^ 2, c ^ 2 + a ^ 2} : Finset ℝ)

    have h_S1_card : S1.card = 3 := by
      -- Prove that {a+b, b+c, c+a} has 3 distinct elements
      simp [S1]
      rw [Finset.card_eq_three]
      use a+b, b+c, c+a
      refine ⟨?_, ?_, ?_, ?_⟩
      . by_contra h
        linarith
      . by_contra h
        linarith
      . by_contra h
        linarith
      . rfl

    have h_S2_card : S2.card = 3 := by
      -- Prove that {a^2+b^2, b^2+c^2, c^2+a^2} has 3 distinct elements
      simp [S2]
      rw [Finset.card_eq_three]
      use a^2+b^2, b^2+c^2, c^2+a^2
      refine ⟨?_, ?_, ?_, ?_⟩
      . by_contra h
        nlinarith
      . by_contra h
        nlinarith
      . by_contra h
        nlinarith
      . rfl

    have h_S1_subset_S: S1 ⊆ S := by
      -- S1 = {a+b, b+c, c+a} ⊆ {a+b, b+c, c+a, a^2+b^2, b^2+c^2, c^2+a^2} = S
      simp [S1, S]
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl
      . exact Finset.mem_insert_self _ _
      . exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      . exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))


    have h_S2_subset_S: S2 ⊆ S := by
      -- S2 = {a^2+b^2, b^2+c^2, c^2+a^2} ⊆ {a+b, b+c, c+a, a^2+b^2, b^2+c^2, c^2+a^2} = S
      simp [S2, S]
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl
      all_goals simp

    have h_S_card : S.card = 3 := by
      apply Finset.card_mono at h_S1_subset_S
      rw [h_S1_card, ← hcard] at h_S1_subset_S
      unfold S
      rw [← hcard]
      omega

    have h_S1_eq_S : S1 = S := by
      apply Finset.eq_of_subset_of_card_le
      . exact h_S1_subset_S
      . rw [h_S1_card, h_S_card]

    have h_S2_eq_S : S2 = S := by
      apply Finset.eq_of_subset_of_card_le
      . exact h_S2_subset_S
      . rw [h_S2_card, h_S_card]

    have h_S1_eq_S2 : S1 = S2 := by
      rw [h_S1_eq_S, h_S2_eq_S]

    -- Key observation: if S1 = S2 and we know their respective minimum elements,
    -- then these minimum elements must be equal
    -- We need to first prove that a+b is indeed the minimum element of S1,
    -- and a^2+b^2 is the minimum element of S2

    -- Based on the conditions a ≥ 0, b ≥ 0, c ≥ 0, a < b < c
    -- a+b is the minimum element in {a+b, b+c, c+a}
    have h_ab_min_S1 : ∀ x ∈ S1, a + b ≤ x := by
      intro x hx
      simp [S1] at hx
      cases' hx with h h
      · exact le_of_eq h.symm
      · cases' h with h h
        · rw [h]
          linarith [hab, hbc]  -- a < b < c implies a+b < b+c
        · rw [h]
          linarith [hab]       -- a < b implies a+b < c+a (when c ≥ b)

    -- a^2+b^2 is the minimum element in {a^2+b^2, b^2+c^2, c^2+a^2}
    have h_a2b2_min_S2 : ∀ x ∈ S2, a^2 + b^2 ≤ x := by
      intro x hx
      simp [S2] at hx
      cases' hx with h h
      · exact le_of_eq h.symm
      · cases' h with h h
        · rw [h]
          -- Need to prove a^2+b^2 ≤ b^2+c^2, i.e., a^2 ≤ c^2
          have h_ac : a ≤ c := le_of_lt (lt_trans hab hbc)
          have h_a2c2 : a^2 ≤ c^2 := sq_le_sq' (by linarith [ha]) h_ac
          linarith
        · rw [h]
          -- Need to prove a^2+b^2 ≤ c^2+a^2, i.e., b^2 ≤ c^2
          have h_bc : b ≤ c := le_of_lt hbc
          have h_b2c2 : b^2 ≤ c^2 := sq_le_sq' (by linarith [hb]) h_bc
          linarith [h_b2c2]  -- a^2 + b^2 ≤ a^2 + c^2 = c^2 + a^2

    -- Now use S1 = S2 and uniqueness of minimum elements
    have h_eq1 : a + b = a^2 + b^2 := by
      -- a+b ∈ S1 = S2, so a+b ∈ S2
      have h1 : a + b ∈ S2 := by
        rw [← h_S1_eq_S2]
        simp [S1]

      -- a^2+b^2 ∈ S2 = S1, so a^2+b^2 ∈ S1
      have h2 : a^2 + b^2 ∈ S1 := by
        rw [h_S1_eq_S2]
        simp [S2]

      -- Since a^2+b^2 is the minimum element of S2, and a+b ∈ S2
      have h3 : a^2 + b^2 ≤ a + b := h_a2b2_min_S2 (a + b) h1

      -- Since a+b is the minimum element of S1, and a^2+b^2 ∈ S1
      have h4 : a + b ≤ a^2 + b^2 := h_ab_min_S1 (a^2 + b^2) h2

      -- Therefore a+b = a^2+b^2
      exact le_antisymm h4 h3

    -- Now prove that the maximum elements are also equal
    -- b+c is the maximum element in {a+b, b+c, c+a}
    have h_bc_max_S1 : ∀ x ∈ S1, x ≤ b + c := by
      intro x hx
      simp [S1] at hx
      cases' hx with h h
      · rw [h]
        linarith [hab, hbc]  -- a+b < b+c because a < c
      · cases' h with h h
        · exact le_of_eq h
        · rw [h]
          linarith [hbc]     -- c+a < b+c because a < b

    -- b^2+c^2 is the maximum element in {a^2+b^2, b^2+c^2, c^2+a^2}
    have h_b2c2_max_S2 : ∀ x ∈ S2, x ≤ b^2 + c^2 := by
      intro x hx
      simp [S2] at hx
      cases' hx with h h
      · rw [h]
        -- Need to prove a^2+b^2 ≤ b^2+c^2, i.e., a^2 ≤ c^2
        have h_ac : a ≤ c := le_of_lt (lt_trans hab hbc)
        have h_a2c2 : a^2 ≤ c^2 := sq_le_sq' (by linarith [ha]) h_ac
        linarith
      · cases' h with h h
        · exact le_of_eq h
        · rw [h]
          -- Need to prove c^2+a^2 ≤ b^2+c^2, i.e., a^2 ≤ b^2
          have h_ab : a ≤ b := le_of_lt hab
          have h_a2b2 : a^2 ≤ b^2 := sq_le_sq' (by linarith [ha]) h_ab
          linarith

    -- Use S1 = S2 and uniqueness of maximum elements to prove b+c = b^2+c^2
    have h_eq2 : b + c = b^2 + c^2 := by
      -- b+c ∈ S1 = S2, so b+c ∈ S2
      have h1 : b + c ∈ S2 := by
        rw [← h_S1_eq_S2]
        simp [S1]

      -- b^2+c^2 ∈ S2 = S1, so b^2+c^2 ∈ S1
      have h2 : b^2 + c^2 ∈ S1 := by
        rw [h_S1_eq_S2]
        simp [S2]

      -- Since b^2+c^2 is the maximum element of S2, and b+c ∈ S2
      have h3 : b + c ≤ b^2 + c^2 := h_b2c2_max_S2 (b + c) h1

      -- Since b+c is the maximum element of S1, and b^2+c^2 ∈ S1
      have h4 : b^2 + c^2 ≤ b + c := h_bc_max_S1 (b^2 + c^2) h2

      -- Therefore b+c = b^2+c^2
      exact le_antisymm h3 h4

    -- Method 1: Set-theoretic proof that the third element is also equal
    -- Since S1 = S2, and S1 = {a+b, b+c, c+a}, S2 = {a^2+b^2, b^2+c^2, c^2+a^2}
    -- We already know a+b = a^2+b^2, b+c = b^2+c^2
    -- Therefore the remaining element must also be equal: c+a = c^2+a^2
    have h_eq3 : c + a = c^2 + a^2 := by
      -- Directly use set equality and elimination
      -- Since S1 = S2, c+a ∈ S1, so c+a ∈ S2
      have h_ca_in_S2 : c + a ∈ S2 := by
        rw [← h_S1_eq_S2]
        simp [S1]

      -- In S2, c+a must equal one of a^2+b^2, b^2+c^2, or c^2+a^2
      simp [S2] at h_ca_in_S2
      cases' h_ca_in_S2 with h h
      · -- If c+a = a^2+b^2, combined with a+b = a^2+b^2, we get c+a = a+b
        -- But this contradicts a < b < c
        exfalso
        have : c + a = a + b := by rw [h, h_eq1.symm]
        linarith [hbc]  -- c+a > a+b because c > b
      · cases' h with h h
        · -- If c+a = b^2+c^2, combined with b+c = b^2+c^2, we get c+a = b+c
          -- But this contradicts a < b
          exfalso
          have : c + a = b + c := by rw [h, h_eq2.symm]
          linarith [hab]  -- c+a < b+c because a < b
        · -- Therefore we must have c+a = c^2+a^2
          exact h

    -- Now we have all three equations:
    -- h_eq1: a + b = a^2 + b^2
    -- h_eq2: b + c = b^2 + c^2
    -- h_eq3: c + a = c^2 + a^2

    have : a-c=a^2-c^2 := by linarith
    have : (a-c)*(a+c-1)=0 := by linarith
    simp at this
    rcases this with h1| h2
    . linarith
    . have : c=1-a := by linarith
      rw [this] at h_eq3
      ring_nf at h_eq3
      have : a * (a-1)=0 := by linarith
      simp at this
      rcases this with h3| h4
      . subst a c
        have : b * (b-1)=0 := by linarith
        simp at this
        rcases this with h5| h6
        . linarith
        . linarith
      . linarith
