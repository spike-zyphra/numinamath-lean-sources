import Mathlib

theorem my_favorite_theorem :
  IsLeast {k : ℕ | 1 < k ∧ ∀ s : Finset ℕ, s ⊆ Finset.Icc 1 100 ∧ s.card = k →
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ Nat.Coprime a b} 51 := by


  constructor
  . simp only [Set.mem_setOf_eq]
    refine ⟨by simp, ?_⟩
    intro s ⟨h1, h2⟩
    by_cases hs1 : 1 ∈ s
    . have : (s \ {1}).card = 50 := by
        rw [Finset.card_sdiff]
        . simp; exact h2
        . simp; exact hs1
      have : (s \ {1}).Nonempty := by
        rw [← Finset.card_pos]
        omega
      have := Finset.Nonempty.exists_mem this
      obtain ⟨b, hb⟩ := this
      use 1
      refine ⟨hs1, ?_⟩
      use b
      simp at hb
      refine ⟨?_, ?_, ?_⟩
      . exact hb.1
      . exact Ne.symm hb.2
      . simp
    . have : ∃ a ∈ s, Odd a := by
        by_contra h
        push_neg at h
        let evens := (Finset.Icc 2 100).filter Even
        have s_sub_evens : s ⊆ evens := by
          intro x hx
          simp [evens]
          constructor
          . -- x ∈ Finset.Icc 2 100
            have := h1 hx
            simp at this
            constructor
            . -- 2 ≤ x
              by_contra hlt
              simp at hlt
              obtain ⟨hx1, hx2⟩ := this
              have : x = 1 := by omega
              subst x
              contradiction
            . exact this.2
          .
            by_contra hodd
            simp at hodd
            have := h x hx hodd
            contradiction

        have evens_card : evens.card = 50 := by
          simp [evens]
          decide
        have : s.card ≤ evens.card := Finset.card_le_card s_sub_evens
        rw [h2, evens_card] at this
        norm_num at this


      obtain ⟨a, ha_in, ha_odd⟩ := this
      use a
      refine ⟨ha_in, ?_⟩
      have := h1 ha_in
      simp at this
      obtain ⟨ha1, ha2⟩ := this
      have : a ≠ 1 := by by_contra; subst a; contradiction
      have : 1 < a := by omega
      let a' := a
      have ha' : a' = a := rfl


      let t := (Finset.Icc 1 100).filter (fun n => n ≠ a ∧ n.Coprime a)
      suffices t.card > 52 by
        have h3 : (s ∩ t).card > 0 := by
          rw [Finset.card_inter]
          have : (s ∪ t) ⊆ Finset.Icc 1 100 := by
            intro x hx
            simp at hx
            rcases hx with h | h
            . exact h1 h
            . unfold t at h
              simp at h
              simp
              exact h.1

          apply Finset.card_mono at this
          rw [show (Finset.Icc 1 100).card = 100 by simp] at this
          omega

        simp at h3
        obtain ⟨b, hb⟩ := h3
        use b
        simp at hb
        obtain ⟨hb1, hb2⟩ := hb
        unfold t at hb2
        simp at hb2
        obtain ⟨⟨hb3, hb4⟩, hb5, hb6⟩ := hb2
        refine ⟨?_, ?_, ?_⟩
        . exact hb1
        . exact Ne.symm hb5
        . rw [Nat.coprime_comm]; exact hb6

      unfold t
      contrapose ha_odd
      interval_cases a
      all_goals try decide
      all_goals contrapose ha_odd; simp; decide


  . simp only [Set.mem_setOf_eq, lowerBounds]
    intro k ⟨hk1, hk2⟩
    by_contra hc
    let s := Finset.image (fun i => 2 * (i + 1)) (Finset.range k)
    have : s ⊆ Finset.Icc 1 100 ∧ s.card = k := by
      constructor
      . unfold s
        intro x hx
        simp at hx
        obtain ⟨i, hi1, hi2⟩ := hx
        simp
        omega
      . unfold s
        rw [Finset.card_image_of_injective]
        . simp
        . intro i j hij
          simp at hij
          exact hij

    have := hk2 s this
    obtain ⟨a, a_in, b, b_in, a_ne_b, h_coprime⟩ := this
    unfold s at a_in b_in
    simp at a_in b_in
    obtain ⟨i, hi1, hi2⟩ := a_in
    obtain ⟨j, hj1, hj2⟩ := b_in
    unfold Nat.Coprime at h_coprime
    rw [← hi2, ← hj2, Nat.gcd_mul_left] at h_coprime
    omega
