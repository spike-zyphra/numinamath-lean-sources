import Mathlib

/- Let $S$ be a subset of $\{1,2,3,\dots,30\}$ with the property that no pair of distinct elements in $S$ has a sum divisible by $5$.  What is the largest possible size of $S$?
$\textbf{(A)}\ 10\qquad\textbf{(B)}\ 13\qquad\textbf{(C)}\ 15\qquad\textbf{(D)}\ 16\qquad\textbf{(E)}\ 18$ -/
theorem number_theory_95080 (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 30)
    (hS' : S.toSet.Pairwise fun m n ↦ ¬(5 ∣ m + n)) :
    S.card ≤ 13 := by classical

  -- Firstly, we notice that there are 6 elements of each residue class modulo 6 in [1, 30]
  have hIcc_mod (r : ℕ) (hr : r < 5) :
      ((Finset.Icc 1 30).filter fun m ↦ m ≡ r [MOD 5]).card = 6 := by
    interval_cases r <;> decide
  -- Since S is a subset, there are at most 6 elements of each residue class modulo 6 in S
  have hS_mod (r : ℕ) (hr : r < 5) : (S.filter fun m ↦ m ≡ r [MOD 5]).card ≤ 6 :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hS)).trans (hIcc_mod r hr).le

  -- There can at most be 1 element that is 0 modulo 5 in S
  -- As two distinct elements would imply they sum to an integer divisible by 5.
  have : (S.filter fun m ↦ m ≡ 0 [MOD 5]).card ≤ 1 := by
    by_contra! h_contra : 1 < _
    obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp h_contra
    rw [Finset.mem_filter] at ha hb
    exact hS' ha.left hb.left hab <| Nat.dvd_of_mod_eq_zero <| ha.right.add hb.right

  -- There can at most be 6 element that is 1 or 4 modulo 5 in S
  -- This is because only elements from one of the two modulo classes could be in S
  -- Otherwise, the elements 1 modulo 5 and 4 modulo 5 add to an integer divisible by 5.
  have hS_14:
      (S.filter fun m ↦ m ≡ 1 [MOD 5]).card
        + (S.filter fun m ↦ m ≡ 4 [MOD 5]).card
          ≤ 6 := by
    by_cases hS₁ : ∃ m ∈ S, m ≡ 1 [MOD 5]
    · have : ∀ m ∈ S, ¬(m ≡ 4 [MOD 5]) := by
        by_contra! hS₄
        obtain ⟨m, hm, hm'⟩ := hS₁
        obtain ⟨n, hn, hn'⟩ := hS₄
        have : m ≠ n := by
          rintro rfl
          have := hn'.symm.trans hm'
          rw [Nat.ModEq] at this
          norm_num at this
        exact hS' hm hn this <| Nat.dvd_of_mod_eq_zero <| hm'.add hn'
      have : (S.filter fun m ↦ m ≡ 4 [MOD 5]).card = 0 := by
        rwa [Finset.card_filter_eq_zero_iff]
      rw [this, add_zero]
      exact hS_mod 1 (by decide)
    · push_neg at hS₁
      have : (S.filter fun m ↦ m ≡ 1 [MOD 5]).card = 0 := by
        rwa [Finset.card_filter_eq_zero_iff]
      rw [this, zero_add]
      exact hS_mod 4 (by decide)

  -- There can at most be 6 element that is 2 or 3 modulo 5 in S
  -- This is because only elements from one of the two modulo classes could be in S
  -- Otherwise, the elements 2 modulo 5 and 3 modulo 5 add to an integer divisible by 5.
  have hS_23:
      (S.filter fun m ↦ m ≡ 2 [MOD 5]).card
        + (S.filter fun m ↦ m ≡ 3 [MOD 5]).card
          ≤ 6 := by
    by_cases hS₁ : ∃ m ∈ S, m ≡ 2 [MOD 5]
    · have : ∀ m ∈ S, ¬(m ≡ 3 [MOD 5]) := by
        by_contra! hS₄
        obtain ⟨m, hm, hm'⟩ := hS₁
        obtain ⟨n, hn, hn'⟩ := hS₄
        have : m ≠ n := by
          rintro rfl
          have := hn'.symm.trans hm'
          rw [Nat.ModEq] at this
          norm_num at this
        exact hS' hm hn this <| Nat.dvd_of_mod_eq_zero <| hm'.add hn'
      have : (S.filter fun m ↦ m ≡ 3 [MOD 5]).card = 0 := by
        rwa [Finset.card_filter_eq_zero_iff]
      rw [this, add_zero]
      exact hS_mod 2 (by decide)
    · push_neg at hS₁
      have : (S.filter fun m ↦ m ≡ 2 [MOD 5]).card = 0 := by
        rwa [Finset.card_filter_eq_zero_iff]
      rw [this, zero_add]
      exact hS_mod 3 (by decide)

  have h_filter_aux {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] :
      (S.filter (fun m ↦ p m ∨ q m)).card ≤ (S.filter p).card + (S.filter q).card := by
    rw [Finset.filter_or]
    apply Finset.card_union_le

  calc
    -- Now, S can be divided into 5 disjoint pieces based on the residue classes
    -- And from the above discussion, we group them into {[0]}, {[1], [4]}, {[2], [3]}
    -- They have ≤ 1, 6, 6 elements in S respectively, so |S| ≤ 13.
    S.card = (S.filter fun m ↦ m ≡ 0 [MOD 5]).card + (S.filter fun m ↦ ¬m ≡ 0 [MOD 5]).card :=
      (Finset.filter_card_add_filter_neg_card_eq_card _).symm
    _ ≤ 1 + (S.filter fun m ↦ ¬m ≡ 0 [MOD 5]).card := by
      gcongr
    _ = 1 + ((S.filter fun m ↦ ¬m ≡ 0 [MOD 5]).filter fun m ↦ (m ≡ 1 [MOD 5] ∨ m ≡ 4 [MOD 5])).card
        + ((S.filter fun m ↦ ¬m ≡ 0 [MOD 5]).filter fun m ↦ ¬(m ≡ 1 [MOD 5] ∨ m ≡ 4 [MOD 5])).card := by
      rw [add_assoc]
      congr 1
      exact (Finset.filter_card_add_filter_neg_card_eq_card _).symm
    _ = 1 + (S.filter fun m ↦ (m ≡ 1 [MOD 5] ∨ m ≡ 4 [MOD 5])).card
        + ((S.filter fun m ↦ ¬m ≡ 0 [MOD 5]).filter fun m ↦ ¬(m ≡ 1 [MOD 5] ∨ m ≡ 4 [MOD 5])).card := by
      congr 3
      ext m
      simp
      intro hm _
      simp_rw [Nat.ModEq] at hm ⊢
      rcases hm with hm | hm <;> (rw [hm]; decide)
    _ = 1 + (S.filter fun m ↦ (m ≡ 1 [MOD 5] ∨ m ≡ 4 [MOD 5])).card
        + (S.filter fun m ↦ (¬m ≡ 0 [MOD 5]) ∧ ¬(m ≡ 1 [MOD 5] ∨ m ≡ 4 [MOD 5])).card := by
      rw [Finset.filter_filter]
    _ = 1 + (S.filter fun m ↦ (m ≡ 1 [MOD 5] ∨ m ≡ 4 [MOD 5])).card
        + (S.filter fun m ↦ (m ≡ 2 [MOD 5] ∨ m ≡ 3 [MOD 5])).card := by
      congr 3
      ext m
      mod_cases m % 5 <;> (simp [Nat.ModEq] at H ⊢; simp_rw [H]; decide)
    _ ≤ 1 + 6 + 6 := by
      gcongr
      · exact h_filter_aux.trans hS_14
      · exact h_filter_aux.trans hS_23