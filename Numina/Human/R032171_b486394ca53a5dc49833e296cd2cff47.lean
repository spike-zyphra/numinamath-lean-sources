import Mathlib

/- Let's prove that among any six irrational numbers, there are always three such that the sum of any two of them is irrational. -/
theorem number_theory_162159 (s : Finset ℝ) (h₀ : s.card = 6)
    (h₁ : ∀ x ∈ s, Irrational x) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Irrational (a + b) ∧
    Irrational (a + c) ∧ Irrational (b + c)
  := by
    -- We'll prove it using graph theory

    -- Create the graph of the six numbers, where two vertices are adjacent iff their
    -- sum is irrational (and the vertices are different).
    let G_irrational : SimpleGraph s := by
      refine SimpleGraph.mk (fun v1 v2 => Irrational (v1 + v2) ∧ v1 ≠ v2) ?_ ?_
      intro aa bb hh
      convert hh using 1
      rw [add_comm]
      exact ne_comm
      intro aa
      simp only [ne_eq, not_true_eq_false, and_false, not_false_eq_true]

    -- The graph has 6 vertices
    have graph_card : Fintype.card { x // x ∈ s } = 6 := by
      simp only [Fintype.card_coe]
      exact h₀

    -- We need a version of Ramsey number R(3, 3) = 6, saying that in a 6 vertex graph,
    -- there is either a triangle, or three vertices where neither is connected
    have ramsey_three : ∀ (A : Type) [Fintype A] (G : SimpleGraph A) (_ : Fintype.card A = 6),
    ∃ a b c, a ≠ b ∧ b ≠ c ∧ c ≠ a
    ∧ ((G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) ∨ (¬G.Adj a b ∧ ¬G.Adj b c ∧ ¬G.Adj c a)) := by
      intro A _ G hcard
      -- wlog, we have some vertex v with atleast 3 adjacent vertices
      wlog hh : (∃ v, 3 ≤ Set.ncard (G.neighborSet v)) generalizing G
      · simp only [not_exists, not_le] at hh
        obtain ⟨v⟩ := Fintype.card_pos_iff.mp <| Nat.lt_of_sub_eq_succ hcard
        replace hh := hh v
        -- if v doesn't have at least 3 neighbours, then it has at least 3 neighbours in its complement
        have comp_card : 3 ≤ (Gᶜ.neighborSet v).ncard := by
          have v_fin := (G.neighborSet v).toFinite
          have v_fin_compl := (G.neighborSet v)ᶜ.toFinite
          rw [SimpleGraph.neighborSet_compl]
          convert_to 3 ≤ ((G.neighborSet v)ᶜ).ncard - 1
          · refine Set.ncard_diff_singleton_of_mem ?_ v_fin_compl
            simp only [Set.mem_compl_iff, SimpleGraph.mem_neighborSet, SimpleGraph.irrefl,
              not_false_eq_true]
          have : (G.neighborSet v).ncard + (G.neighborSet v)ᶜ.ncard = 6 := by
            rw [←hcard, Fintype.card_eq_nat_card]
            exact Set.ncard_add_ncard_compl _ v_fin v_fin_compl
          omega

        -- It's true in the complement graph
        obtain ⟨a, b, c, h1, h2, h3, hhh⟩ := this Gᶜ ⟨v, comp_card⟩
        simp only [SimpleGraph.compl_adj, not_not] at hhh
        refine ⟨a, b, c, h1, h2, h3, ?_⟩
        tauto

      obtain ⟨v, vh⟩ := hh

      -- let a b c be vertices adjacent to v
      have fin := Set.toFinite (G.neighborSet v)
      obtain ⟨a, ah, b, bh, c, ch, abh, ach, bch⟩ := (Set.two_lt_ncard fin).mp vh
      rw [SimpleGraph.mem_neighborSet] at ah bh ch
      by_cases hm : G.Adj a b ∨ G.Adj b c ∨ G.Adj c a
      -- if any of them are adjecent to another, then we have a triangle of adjacent vertices
      · rcases hm with ad1 | ad2 | ad3
        · exact ⟨a, b, v, abh, bh.ne', ah.ne, Or.inl ⟨ad1, bh.symm, ah⟩⟩
        · exact ⟨v, b, c, bh.ne, ad2.ne, ch.ne', Or.inl ⟨bh, ad2, ch.symm⟩⟩
        · exact ⟨a, v, c, ah.ne', ch.ne, ad3.ne, Or.inl ⟨ah.symm, ch, ad3⟩⟩
      -- if none of them are adjacent, they form a triple of non-adjacent vertices
      · simp only [not_or] at hm
        exact ⟨a, b, c, abh, bch, ach.symm, Or.inr hm⟩

    -- apply the theorem to our case
    obtain ⟨a, b, c, abh, bch, cah, hhh⟩ := ramsey_three { x // x ∈ s } G_irrational graph_card
    refine ⟨a, Finset.coe_mem a, b, Finset.coe_mem b, c, Finset.coe_mem c, ?_, ?_, ?_, ?_⟩
    exact Subtype.coe_ne_coe.mpr abh
    exact Subtype.coe_ne_coe.mpr cah.symm
    exact Subtype.coe_ne_coe.mpr bch

    cases' hhh with all none
    -- if we have a triangle, then we have three numbers pairwise irrational
    · simp only [ne_eq] at all
      have ⟨aa, bb, ⟨cc1, cc2⟩⟩ := all
      exact ⟨aa.1, add_comm (c : ℝ) a ▸ cc1, bb.1⟩
    -- if we don't have a triangle, then we'll find a contradiction
    · simp only [abh, bch, cah, ne_eq, not_false_eq_true, and_true] at none
      -- consider (1 / 2) * ((a + b) + (c + a) - (b + c)) = a
      have eqq : (1 / 2 : ℚ) * ((a + b : ℝ) + (c + a : ℝ) - (b + c : ℝ)) = a := by linarith
      -- then left side is rational
      have lhs_rat : ¬Irrational ((1 / 2 : ℚ) * ((a + b : ℝ) + (c + a : ℝ) - (b + c : ℝ))) := by
        simp only [Irrational, Set.mem_range, not_exists, not_forall, Decidable.not_not] at none
        -- because pairwise sums are rational
        obtain ⟨⟨abp, abph⟩, ⟨bcp, bcph⟩, ⟨cap, caph⟩⟩ := none
        -- and multiplication and addition preserves rationality
        rw [←abph, ←bcph, ←caph, irrational_rat_mul_iff]
        simp only [one_div, ne_eq, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
          irrational_sub_rat_iff, irrational_add_rat_iff, Rat.not_irrational, and_false]
      -- but right side is irrational
      have rhs_irrat : Irrational a := by
        exact h₁ a <| Finset.coe_mem a

      -- contradiction
      rw [eqq] at lhs_rat
      contradiction