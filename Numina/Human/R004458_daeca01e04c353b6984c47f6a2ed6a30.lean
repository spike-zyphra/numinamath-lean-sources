import Mathlib

/- 7. The player numbers of a sports team are uniquely selected from the positive integers 1 to 100. If the number of any player is neither the sum of the numbers of any other two players nor twice the number of another player, then the maximum number of players on this team is $\qquad$ people. -/
theorem number_theory_609447 :
    IsGreatest {n | ∃ S, S ⊆ Finset.Icc 1 100 ∧ (∀ x ∈ S, ∀ a ∈ S, ∀ b ∈ S, x ≠ a ∧ x ≠ b ∧ a ≠ b → x ≠ a + b) ∧ (∀ x ∈ S, ∀ a ∈ S, x ≠ a → x ≠ 2 * a) ∧ n = S.card} 50 := by
  -- The proof consists of two parts: showing 50 is a possible size, and that no size greater than 50 is possible.
  constructor
  -- Part 1: Show that a set of size 50 with the given properties exists.
  · simp
    -- We propose the set of all odd numbers between 1 and 100.
    use Finset.Icc 1 100 |>.filter (fun x => Odd x)
    -- Simplify the goal after providing the set.
    simp
    -- We now need to prove the two properties for this set and that its size is 50.
    constructor
    -- First, prove the 3-sum-free property.
    · intro x hx1 hx2 hx3 a ha1 ha2 ha3 b hb1 hb2 hb3 hxa hxb hab
      -- The sum of two odd numbers (a and b) is even.
      have : Even (a + b) := by exact Odd.add_odd ha3 hb3
      -- Assume for contradiction that x = a + b.
      by_contra h
      -- Since x is odd, it cannot be even. But if x = a + b, it must be even.
      rw [h, ← Nat.not_even_iff_odd] at hx3
      -- This is a contradiction.
      exact hx3 this
    -- Now, prove the second property and the cardinality.
    · constructor
      -- First, prove that no element is double another.
      · intro x hx1 hx2 hx3 a ha1 ha2 ha3 hxa
        -- Assume for contradiction that x = 2 * a.
        by_contra h
        -- This implies x is even, which contradicts that x is odd.
        simp [h, ← Nat.not_even_iff_odd] at hx3
      -- Finally, prove that the cardinality of the set is 50. `decide` solves this.
      · decide
  -- Part 2: Show that for any set S with the given properties, its size n is at most 50.
  · rintro n ⟨S, hS, h1, h2, h3⟩
    -- Assume for contradiction that n > 50.
    by_contra! h
    -- The set S must be non-empty, otherwise its card would be 0, not > 50.
    have h_nonempty : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty
      rw [h_empty, Finset.card_empty] at h3
      rw [h3] at h
      linarith
    -- Combine the two sum-free conditions into a single statement: a + b ∉ S for a, b ∈ S.
    have h_sum_free : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S := by
      intro a ha b hb h_sum_in_S
      let x := a + b
      have hx : x ∈ S := h_sum_in_S
      -- All elements in S are positive.
      have h_pos : ∀ z ∈ S, 0 < z := by
        intro z hz
        suffices z ∈ Finset.Icc 1 100 by
          exact Finset.mem_Icc.1 this |>.1
        tauto
      -- Consider two cases: a = b and a ≠ b.
      by_cases h_a_eq_b : a = b
      -- Case a = b. Then x = 2 * a.
      · subst h_a_eq_b
        -- Since a > 0, x ≠ a.
        have h_a_ne_2a : x ≠ a := by
          specialize h_pos a ha
          omega
        -- This contradicts property h2.
        specialize h2 x hx a ha h_a_ne_2a
        simp [x, two_mul] at h2
      -- Case a ≠ b.
      · -- In this case, x, a, and b are all distinct.
        have h_distinct : x ≠ a ∧ x ≠ b ∧ a ≠ b := by
          constructor
          · simp [x]
            linarith [h_pos b hb]
          · constructor
            · simp [x]
              linarith [h_pos a ha]
            · exact h_a_eq_b
        -- This contradicts property h1.
        exact h1 x hx a ha b hb h_distinct rfl
    -- Let k be the maximum element in S.
    let k := S.max' h_nonempty
    -- k is an element of S.
    have hk : k ∈ S := Finset.max'_mem S h_nonempty
    -- Every element of S is less than or equal to k.
    have hk1 := Finset.le_max' S
    -- Define a function f(s) = k - s for s in S.
    let f : ℕ → ℕ := fun s => if s ≤ k then k - s else 0
    -- This function is injective on S.
    have h_inj : Set.InjOn f S := by
      intro s₁ hs₁ s₂ hs₂ h_eq
      simp [f] at h_eq hs₁ hs₂
      have hs₁' : s₁ ≤ k := by exact hk1 s₁ hs₁
      have hs₂' : s₂ ≤ k := by exact hk1 s₂ hs₂
      simp [hs₁', hs₂'] at h_eq
      omega
    -- Let T be the image of S under f.
    let T := S.image f
    -- T has the same cardinality as S because f is injective on S.
    have hT_card : T.card = S.card := by
      exact Finset.card_image_iff.mpr h_inj
    -- The sets S and T are disjoint.
    have h_disjoint : Disjoint S T := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      apply Finset.eq_empty_of_forall_not_mem
      -- Assume x is in the intersection of S and T.
      intro x hx_inter
      rw [Finset.mem_inter] at hx_inter
      rcases hx_inter with ⟨hxS, hxT⟩
      -- If x is in T, then x = k - s for some s in S.
      rw [Finset.mem_image] at hxT
      rcases hxT with ⟨s, hs, h_x_eq_ks⟩
      -- This implies x + s = k.
      have h_sum_eq_k : x + s = k := by
        simp [f] at h_x_eq_ks
        suffices s ≤ k by
          simp [this] at h_x_eq_ks
          omega
        exact hk1 s hs
      -- But the sum of two elements of S cannot be in S.
      have h_sum_notin_S := h_sum_free x hxS s hs
      -- So k cannot be in S.
      rw [h_sum_eq_k] at h_sum_notin_S
      -- This is a contradiction, as k is the maximum element of S.
      exact h_sum_notin_S hk
    -- The cardinality of the union of disjoint sets is the sum of their cardinalities.
    have h_union_card : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint h_disjoint
    -- Thus, the cardinality of the union is 2n.
    rw [hT_card, ← h3, ← two_mul] at h_union_card
    -- The union of S and T is a subset of the integers from 0 to k.
    have h_union_subset : S ∪ T ⊆ Finset.Icc 0 k := by
      apply Finset.union_subset
      -- Proof that S is a subset of [0, k].
      · intro x hx; simp only [Finset.mem_Icc]
        constructor
        · exact zero_le x
        · exact hk1 x hx
      -- Proof that T is a subset of [0, k].
      · intro x hx; rw [Finset.mem_image] at hx
        rcases hx with ⟨s, hs, rfl⟩
        simp only [Finset.mem_Icc]
        constructor
        · exact Nat.zero_le (f s)
        · simp [f]
          suffices s ≤ k by
            simp [this]
          exact hk1 s hs
    -- The cardinality of a subset is less than or equal to the cardinality of the superset.
    have h_card_le : (S ∪ T).card ≤ (Finset.Icc 0 k).card := Finset.card_le_card h_union_subset
    -- This gives the inequality 2n ≤ k + 1.
    rw [h_union_card] at h_card_le
    simp at h_card_le
    -- The maximum element k is at most 100.
    have hk_le_100 : k ≤ 100 := by
      suffices k ∈ Finset.Icc 1 100 by
        exact Finset.mem_Icc.1 this |>.2
      tauto
    -- Combining 2n ≤ k + 1 and k ≤ 100 gives 2n ≤ 101.
    have h_2n_le_101 : 2 * n ≤ 101 := by linarith [h_card_le, hk_le_100]
    -- Since n is an integer, n must be at most 50.
    have h_n_le_50 : n ≤ 50 := by omega
    -- This contradicts our initial assumption that n > 50.
    omega